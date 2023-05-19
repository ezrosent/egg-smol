//! When executing a join, some indexes are cached long-term while some are
//! generated on the fly.
//!
//! The logic behind both of these is tracked by the `IndexCache` type.
use smallvec::SmallVec;

use crate::{
    common::HashMap,
    free_join::AtomIdx,
    function::{index::IndexArg, offsets::Offset},
    pool::{Clear, Pool, PoolSet, SharedPoolRef},
    schema::FunctionId,
};

use super::{
    index::{ConstantIndex, ConstantIndexArg, Index},
    offsets::{OffsetRange, Offsets, RangeOrSlice, SortedOffsetSlice},
    table::{Generation, Table},
    Value,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct IndexCacheKey<T> {
    func: FunctionId,
    index_on: T,
    eqs: Box<[(AtomIdx, AtomIdx)]>,
}

// TODO: use RawTable here to avoid allocations on lookups.
type IndexMemo<'a, Arg, V> = HashMap<IndexCacheKey<SmallVec<[Arg; 3]>>, IndexState<'a, V>>;

pub(crate) struct IndexCache<'a> {
    column_indexes: IndexMemo<'a, AtomIdx, Index<'a>>,
    constant_indexes: IndexMemo<'a, (AtomIdx, Value), ConstantIndex<'a>>,
    index_pool: &'a Pool<Index<'a>>,
    constant_pool: &'a Pool<ConstantIndex<'a>>,
}

#[derive(Debug)]
pub(crate) struct IndexCacheResult<'a, T: Clear> {
    /// The actual index matching the cache query.
    pub(crate) index: SharedPoolRef<'a, T>,
    /// Whether or not the index is precise. If the index is not precise, it may
    /// overapproximate the offsets in the requested range.
    pub(crate) precise: bool,
}

impl<'a, T: Clear> Clone for IndexCacheResult<'a, T> {
    fn clone(&self) -> Self {
        IndexCacheResult {
            index: self.index.clone(),
            precise: self.precise,
        }
    }
}

impl<'a, T: Clear> IndexCacheResult<'a, T> {
    fn new(index: SharedPoolRef<'a, T>, precise: bool) -> Self {
        IndexCacheResult { index, precise }
    }
}

struct IndexState<'a, T: Clear> {
    // NB: we should probably migrate Rc to a custom SharedPoolRef type that
    // handles shared ownership.
    data: SharedPoolRef<'a, T>,
    gen: Generation,
    up_to: Offset,
}

impl<'a> IndexCache<'a> {
    pub(crate) fn new(pool_set: &PoolSet<'a>) -> IndexCache<'a> {
        IndexCache {
            column_indexes: HashMap::default(),
            constant_indexes: HashMap::default(),
            index_pool: pool_set.get(),
            constant_pool: pool_set.get(),
        }
    }

    pub(crate) fn get_index<'b, 'c: 'b>(
        &mut self,
        id: FunctionId,
        cols: &[AtomIdx],
        eqs: &[(AtomIdx, AtomIdx)],
        tables: impl Fn(FunctionId) -> &'b Table<'c>,
        offsets: &RangeOrSlice<&SortedOffsetSlice>,
    ) -> IndexCacheResult<'a, Index<'a>> {
        let Some((low, high)) = offsets.bounds() else {
            // The offset range is empty: just return an empty index
            return IndexCacheResult::new(self.index_pool.get(&IndexArg {
                cols,
                eqs,
            }).into_shared(), true);
        };

        let table = tables(id);
        if low != Offset::new(0) || offsets.is_slice() {
            // Heuristic: we only cache dense ranges that start at 0. This ensures
            // that we cover the largest ranges, which are the ones that are
            // most important to cache and the safest to overapproximate.
            let mut result = self.index_pool.get(&IndexArg { cols, eqs });
            result.extend(table, offsets);
            return IndexCacheResult::new(result.into_shared(), true);
        }
        let key = IndexCacheKey {
            func: id,
            index_on: cols.into(),
            eqs: eqs.into(),
        };

        let state = self.column_indexes.entry(key).or_insert_with(|| {
            let mut result = self.index_pool.get(&IndexArg { cols, eqs });
            result.extend(table, offsets);
            IndexState {
                data: result.into_shared(),
                gen: table.generation(),
                up_to: high,
            }
        });

        let data_mut = SharedPoolRef::make_mut(&mut state.data);

        if table.generation() != state.gen {
            // The table has been rehashed we last cached this index. Recompute
            // it.
            data_mut.clear_data();
            data_mut.extend(table, &OffsetRange::new(Offset::new(0), high));
            state.gen = table.generation();
            state.up_to = high;
        }
        if high > state.up_to {
            data_mut.extend(table, &OffsetRange::new(state.up_to, high));
            state.up_to = high;
        }
        IndexCacheResult::new(state.data.clone(), high == state.up_to)
    }

    pub(crate) fn get_constant_index<'b, 'c: 'b>(
        &mut self,
        id: FunctionId,
        cols: &[(AtomIdx, Value)],
        eqs: &[(AtomIdx, AtomIdx)],
        tables: impl Fn(FunctionId) -> &'b Table<'c>,
        offsets: &RangeOrSlice<&SortedOffsetSlice>,
    ) -> IndexCacheResult<'a, ConstantIndex<'a>> {
        let Some((low, high)) = offsets.bounds() else {
            // The offset range is empty: just return an empty index
            return IndexCacheResult::new(self.constant_pool.get(&ConstantIndexArg {
                cols,
                eqs,
            }).into_shared(), true);
        };

        let table = tables(id);
        if low != Offset::new(0) || offsets.is_slice() {
            // Heuristic: we only cache dense ranges that start at 0. This ensures
            // that we cover the largest ranges, which are the ones that are
            // most important to cache and the safest to overapproximate.
            let mut result = self.constant_pool.get(&ConstantIndexArg { cols, eqs });
            result.extend(table, offsets);
            return IndexCacheResult::new(result.into_shared(), true);
        }
        let key = IndexCacheKey {
            func: id,
            index_on: cols.into(),
            eqs: eqs.into(),
        };

        let state = self.constant_indexes.entry(key).or_insert_with(|| {
            let mut result = self.constant_pool.get(&ConstantIndexArg { cols, eqs });
            result.extend(table, offsets);
            IndexState {
                data: result.into_shared(),
                gen: table.generation(),
                up_to: high,
            }
        });

        let data_mut = SharedPoolRef::make_mut(&mut state.data);

        if table.generation() != state.gen {
            // The table has been rehashed we last cached this index. Recompute
            // it.
            data_mut.clear_data();
            data_mut.extend(table, &OffsetRange::new(Offset::new(0), high));
            state.gen = table.generation();
            state.up_to = high;
        }
        if high > state.up_to {
            data_mut.extend(table, &OffsetRange::new(state.up_to, high));
            state.up_to = high;
        }
        IndexCacheResult::new(state.data.clone(), high == state.up_to)
    }
}

//! Indexes on a subset of columns from a table.

use std::{
    fmt::{self, Debug},
    mem,
};

use smallvec::SmallVec;

use crate::{
    common::{HashMap, NumericId},
    free_join::AtomIdx,
    pool::{Clear, Pool, SharedPoolRef},
};

use super::{
    offsets::{Offsets, SortedOffsetSlice, SortedOffsetVector},
    table::Table,
    Value,
};

/// An index on a particular set of columns for a table.
///
/// Given a [`Table`] `t`, and `Index` is used to store the set of offsets
/// present for each combination of values for the given columns. For example,
/// building an `Index` for a relation `E(x, y)` on column `0` would store the
/// offsets of all `y`s corresponding to each `x`.
///
/// `Index`es can also have a set of equality constraints that must be
/// satisfied, so for a relation `R(x, y, z)` with an `Index` on column `0` such
/// that `x = y`, will return all table offsets where `x = y`, indexed on each
/// unique value of `x`.
#[derive(Clone)]
pub(crate) struct Index<'a> {
    cols: Vec<AtomIdx>,
    eqs: Vec<(AtomIdx, AtomIdx)>,
    data: HashMap<SmallVec<[Value; 4]>, SharedPoolRef<'a, SortedOffsetVector>>,
    pool: &'a Pool<SortedOffsetVector>,
}

impl<'a> Debug for Index<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Index")
            .field("cols", &self.cols)
            .field("eqs", &self.eqs)
            .field("data", &self.data)
            .finish()
    }
}

pub(crate) struct IndexArg<'a> {
    pub cols: &'a [AtomIdx],
    pub eqs: &'a [(AtomIdx, AtomIdx)],
}

impl<'a> Clear for Index<'a> {
    type Factory = &'a Pool<SortedOffsetVector>;
    type Args<'b> = IndexArg<'b>;
    fn construct(&mut self, arg: &IndexArg) {
        self.cols.extend_from_slice(arg.cols);
        self.eqs.extend_from_slice(arg.eqs);
    }
    fn new(f: &Self::Factory) -> Self {
        Index {
            cols: Default::default(),
            eqs: Default::default(),
            data: Default::default(),
            pool: f,
        }
    }
    fn clear(&mut self) {
        self.cols.clear();
        self.eqs.clear();
        self.data.clear();
    }
}

impl<'a> Index<'a> {
    /// Build an index keyed by the given columns, reading the table at the
    /// given offsets and only indexing rows where the given columns are equal.
    ///
    /// This is a thin wrapper around [`Index::extend`]; it is used in tests.
    #[cfg(test)]
    pub(crate) fn new(
        pool: &'a Pool<SortedOffsetVector>,
        cols: Vec<AtomIdx>,
        eqs: Vec<(AtomIdx, AtomIdx)>,
        table: &Table,
        offsets: &impl Offsets,
    ) -> Index<'a> {
        let data = HashMap::default();
        let mut res = Index {
            cols,
            eqs,
            data,
            pool,
        };
        res.extend(table, offsets);
        res
    }

    /// Clear the contents of the index.
    ///
    /// Unlike [`Clear::clear`], this does not clear the columns and equalities
    /// and so the table can immediately have [`Index::extend`] called on it
    /// again.
    pub(crate) fn clear_data(&mut self) {
        self.data.clear();
    }

    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&[Value], &SortedOffsetSlice)> {
        self.data.iter().map(|(k, v)| (k.as_slice(), v.slice()))
    }

    pub(crate) fn get(&self, key: &[Value]) -> Option<SharedPoolRef<'a, SortedOffsetVector>> {
        Some(self.data.get(key)?.clone())
    }

    pub(crate) fn extend(&mut self, table: &Table, offsets: &impl Offsets) {
        let mut key = SmallVec::new();
        offsets.iter_table(table, |offset, args, value| {
            for (l, r) in &self.eqs {
                let v1 = get_col(args, value, *l);
                let v2 = get_col(args, value, *r);
                if v1 != v2 {
                    return;
                }
            }
            for col in self.cols.iter().copied() {
                key.push(get_col(args, value, col));
            }
            SharedPoolRef::make_mut(
                self.data
                    .raw_entry_mut()
                    .from_key(&key)
                    .or_insert_with(|| (mem::take(&mut key), self.pool.get_default().into_shared()))
                    .1,
            )
            .push(offset);
            key.clear();
        });
    }
}

/// A variant of [`Index`] that stores the offsets in a given table that match a
/// specific set of constants.
#[derive(Clone)]
pub(crate) struct ConstantIndex<'a> {
    cols: Vec<(AtomIdx, Value)>,
    eqs: Vec<(AtomIdx, AtomIdx)>,
    data: SharedPoolRef<'a, SortedOffsetVector>,
}

impl<'a> ConstantIndex<'a> {
    /// Add update the constant index with the contents of the table at the given offsets.
    ///
    /// # Panics
    /// This method will panic if the given offsets are not all greater than or
    /// equal to any offsets already in the index.
    pub(crate) fn extend(&mut self, table: &Table, offsets: &impl Offsets) {
        let mut key = SmallVec::<[Value; 4]>::new();
        let target: SmallVec<[Value; 4]> = self.cols.iter().map(|(_, v)| *v).collect();
        let data_mut = SharedPoolRef::make_mut(&mut self.data);
        offsets.iter_table(table, |offset, args, value| {
            for (l, r) in &self.eqs {
                let v1 = get_col(args, value, *l);
                let v2 = get_col(args, value, *r);
                if v1 != v2 {
                    return;
                }
            }
            for (col, _) in self.cols.iter().copied() {
                key.push(get_col(args, value, col));
            }
            if key == target {
                data_mut.push(offset);
            }
            key.clear();
        });
    }

    /// Get the table offsets corresponding to the constants for this index.
    pub(crate) fn offsets(&self) -> &SortedOffsetSlice {
        self.data.slice()
    }

    /// Clear the contents of the index.
    ///
    /// Unlike [`Clear::clear`], this does not clear the columns and equalities
    /// and so the table can immediately have [`Index::extend`] called on it
    /// again.
    pub(crate) fn clear_data(&mut self) {
        SharedPoolRef::make_mut(&mut self.data).clear();
    }
}

impl<'a> Debug for ConstantIndex<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ConstantIndex")
            .field("cols", &self.cols)
            .field("eqs", &self.eqs)
            .field("data", &self.data)
            .finish()
    }
}

pub(crate) struct ConstantIndexArg<'a> {
    pub cols: &'a [(AtomIdx, Value)],
    pub eqs: &'a [(AtomIdx, AtomIdx)],
}

impl<'a> Clear for ConstantIndex<'a> {
    type Factory = &'a Pool<SortedOffsetVector>;
    type Args<'b> = ConstantIndexArg<'b>;
    fn construct(&mut self, arg: &ConstantIndexArg) {
        self.cols.extend_from_slice(arg.cols);
        self.eqs.extend_from_slice(arg.eqs);
    }
    fn new(f: &Self::Factory) -> Self {
        ConstantIndex {
            cols: Default::default(),
            eqs: Default::default(),
            data: f.get_default().into_shared(),
        }
    }
    fn clear(&mut self) {
        self.cols.clear();
        self.eqs.clear();
        SharedPoolRef::make_mut(&mut self.data).clear();
    }
}

/// Get the given numeric column from the given key or value.
pub(crate) fn get_col(key: &[Value], val: Value, col: AtomIdx) -> Value {
    debug_assert!(col.index() <= key.len());
    let i = col.index();
    if i >= key.len() {
        val
    } else {
        key[i]
    }
}

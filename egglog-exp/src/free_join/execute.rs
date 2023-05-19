//! Execute a free join plan using seminaive evaluation.
use smallvec::SmallVec;

use crate::{
    common::{DenseIdMap, HashSet, NumericId},
    free_join::{
        offset_frame::{OffsetFrame, Slot},
        plan::JoinStage,
        AtomId, Query, Variable,
    },
    function::{
        index::get_col,
        index::Index,
        index_cache::{IndexCache, IndexCacheResult},
        offsets::Offsets,
        offsets::{RangeOrSlice, SortedOffsetSlice, SortedOffsetVector},
        table::Timestamp,
        Function, Value,
    },
    pool::{Clear, PoolRef, PoolSet, SharedPoolRef},
    schema::FunctionId,
};

use super::plan::PlanStrategy;

const CHUNK_SIZE: usize = 1024;

/// The updates to a given frame for a single recursive call.
#[derive(Default, Debug)]
pub(crate) struct FrameUpdate<'a> {
    bindings: Vec<(Variable, Value)>,
    updates: Vec<(AtomId, SharedPoolRef<'a, SortedOffsetVector>)>,
}

impl<'a> Clear for FrameUpdate<'a> {
    type Args<'b> = ();
    type Factory = ();

    fn new(_: &()) -> Self {
        FrameUpdate::default()
    }

    fn reuse(&self) -> bool {
        self.updates.reuse()
    }

    fn clear(&mut self) {
        self.bindings.clear();
        self.updates.clear();
    }
}

pub(crate) type UpdateBatch<'a> = Vec<PoolRef<'a, FrameUpdate<'a>>>;

/// A half-open range of timestamps.
#[derive(Copy, Clone, Debug)]
pub(crate) struct TimestampRange {
    pub(crate) low: Timestamp,
    pub(crate) high: Timestamp,
}

pub(crate) struct Runner<'outer, 'pool> {
    timestamps: TimestampRange,
    strategy: PlanStrategy,
    funcs: &'outer DenseIdMap<FunctionId, Function<'pool>>,
    index_cache: &'outer mut IndexCache<'pool>,
    pool_set: &'outer PoolSet<'pool>,
}

impl<'outer, 'a> Runner<'outer, 'a> {
    pub(crate) fn new(
        timestamps: TimestampRange,
        strategy: PlanStrategy,
        funcs: &'outer DenseIdMap<FunctionId, Function<'a>>,
        index_cache: &'outer mut IndexCache<'a>,
        pool_set: &'outer PoolSet<'a>,
    ) -> Runner<'outer, 'a> {
        Runner {
            timestamps,
            strategy,
            funcs,
            index_cache,
            pool_set,
        }
    }
    pub(crate) fn run(&mut self, query: &Query, mut f: impl FnMut(&DenseIdMap<Variable, Value>)) {
        let all = TimestampRange {
            low: Timestamp::new(0),
            high: self.timestamps.high,
        };
        let new = self.timestamps;
        let old = TimestampRange {
            low: Timestamp::new(0),
            high: self.timestamps.low,
        };
        let mut offsets: Vec<Slot<'a, &SortedOffsetSlice>> =
            Vec::with_capacity(query.atoms.n_ids());
        for (atom_id, atom) in query.atoms.iter() {
            let range = self.funcs[atom.func()]
                .table()
                .timestamp_range(all.low, all.high);
            debug_assert_eq!(atom_id.index(), offsets.len());
            offsets.push(Slot::new(RangeOrSlice::Range(range)));
        }
        for (atom_id, atom) in query.atoms.iter() {
            let range = self.funcs[atom.func()]
                .table()
                .timestamp_range(new.low, new.high);
            if range.size() == 0 {
                continue;
            }
            offsets[atom_id.index()] = Slot::new(RangeOrSlice::Range(range));

            {
                let mut frame = OffsetFrame::new(&mut offsets, self.pool_set.get());
                self.execute_frame(query, &mut frame, &mut f);
            }
            let range = self.funcs[atom.func()]
                .table()
                .timestamp_range(old.low, old.high);
            if range.size() == 0 {
                break;
            }
            offsets[atom_id.index()] = Slot::new(RangeOrSlice::Range(range));
        }
    }

    fn execute_frame<'parent, 'cur>(
        &mut self,
        query: &Query,
        frame: &mut OffsetFrame<'a, 'parent, 'cur>,
        f: &mut impl FnMut(&DenseIdMap<Variable, Value>),
    ) {
        let planner = query.plan(
            self.strategy,
            frame
                .iter()
                .map(|(atom, slot)| (atom, slot.offsets().size())),
        );
        self.execute_plan(
            &planner.stages,
            query,
            &mut self.pool_set.get_default::<DenseIdMap<Variable, Value>>(),
            frame,
            f,
        )
    }

    fn execute_plan<'parent, 'cur>(
        &mut self,
        stages: &[JoinStage],
        query: &Query,
        out: &mut DenseIdMap<Variable, Value>,
        frame: &mut OffsetFrame<'a, 'parent, 'cur>,
        f: &mut impl FnMut(&DenseIdMap<Variable, Value>),
    ) {
        let Some((cur, rest)) = stages.split_first() else {
            f(out);
            return;
        };
        match cur {
            JoinStage::ConstantEq {
                atom,
                constants,
                eqs,
            } => {
                let func = query.atoms[*atom].func();
                let IndexCacheResult { index, precise } = self.index_cache.get_constant_index(
                    func,
                    constants,
                    eqs,
                    |func| self.funcs[func].table(),
                    frame[atom.index()].offsets(),
                );

                // If we lack precise offset information, re-filter
                let mut filtered = self.pool_set.get_default::<SortedOffsetVector>();
                if !precise {
                    let (low, hi) = frame[atom.index()]
                        .offsets()
                        .bounds()
                        .expect("empty ranges should have precise offsets");
                    index.offsets().iter().for_each(|o| {
                        if o >= low && o < hi {
                            filtered.push(o)
                        }
                    });
                }

                frame.with_narrowed(|child| {
                    if precise {
                        child.replace(atom.index(), RangeOrSlice::Slice(index.offsets()));
                    } else {
                        child.replace(atom.index(), RangeOrSlice::Slice(filtered.slice()));
                    }
                    self.execute_plan(rest, query, out, child, f);
                });
            }
            JoinStage::Intersect {
                cover,
                bind,
                to_intersect,
            } => {
                //  First, build indexes
                let mut indexes =
                    self.pool_set
                        .get_default::<Vec<(AtomId, IndexCacheResult<'a, Index<'a>>, usize)>>();
                for (i, (scan, _)) in to_intersect.iter().enumerate() {
                    let atom = scan.to_index.atom;
                    let func = query.atoms[atom].func();
                    let result = frame[atom.index()].get_index(|| {
                        self.index_cache.get_index(
                            func,
                            &scan.to_index.vars,
                            &scan.constrain_eq,
                            |func| self.funcs[func].table(),
                            frame[atom.index()].offsets(),
                        )
                    });
                    indexes.push((scan.to_index.atom, result, i));
                }
                let table = self.funcs[query.atoms[cover.to_index.atom].func()].table();
                let offs = frame[cover.to_index.atom.index()].offsets().clone();
                // We only need to recur for the first unique combination of
                // values that we see in the cover, the other recursive calls
                // would yield identical results. This set is used to dedup.
                let mut seen_combination =
                    self.pool_set.get_default::<HashSet<SmallVec<[Value; 4]>>>();
                let mut updates = self.pool_set.get_default::<UpdateBatch<'a>>();
                for chunk in offs.chunks(CHUNK_SIZE) {
                    chunk.iter_table(table, |_, k, v| {
                        // evaluate any equality constraints
                        for (l, r) in &cover.constrain_eq {
                            if get_col(k, v, *l) != get_col(k, v, *r) {
                                return;
                            }
                        }
                        // see if we have seen these variables before.
                        let mut key = SmallVec::<[Value; 4]>::new();
                        for ix in &cover.to_index.vars {
                            key.push(get_col(k, v, *ix));
                        }
                        if !seen_combination.insert(key) {
                            return;
                        }

                        let mut res = self.pool_set.get_default::<FrameUpdate<'a>>();

                        let mut index_key = SmallVec::<[Value; 4]>::new();

                        // Filter the other participants in this stage
                        for (atom, IndexCacheResult { index, precise }, to_compare) in
                            indexes.iter()
                        {
                            let to_compare = &to_intersect[*to_compare].1;
                            for ix in to_compare.iter().copied() {
                                index_key.push(get_col(k, v, ix));
                            }
                            let Some(mut offs) = index.get(&index_key) else {
                                // Intersection is empty
                                return;
                            };
                            match frame[atom.index()].offsets() {
                                RangeOrSlice::Range(r) => {
                                    if !precise {
                                        let (low, hi) = r.bounds().unwrap();
                                        SharedPoolRef::make_mut(&mut offs)
                                            .retain(|o| o >= low && o < hi)
                                    }
                                }
                                RangeOrSlice::Slice(_) => {
                                    debug_assert!(precise);
                                }
                            }
                            res.updates.push((*atom, offs));
                            index_key.clear();
                        }
                        // The intersection is non-empty. Bind the variables
                        for (ix, var) in bind {
                            res.bindings.push((*var, get_col(k, v, *ix)));
                        }
                        updates.push(res)
                    });
                    for update in updates.drain(..) {
                        frame.with_narrowed(|frame| {
                            if !rest.is_empty() {
                                for (atom, offs) in &update.updates {
                                    frame.replace(atom.index(), RangeOrSlice::Slice(offs.slice()))
                                }
                            }
                            for (var, val) in &update.bindings {
                                out.insert(*var, *val);
                            }
                            self.execute_plan(rest, query, out, frame, f)
                        });
                    }
                }
            }
        }
    }
}

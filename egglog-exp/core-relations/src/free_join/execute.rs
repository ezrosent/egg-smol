//! Core free join execution.

use std::{
    hash::{Hash, Hasher},
    iter,
    rc::Rc,
    time::{Duration, Instant},
};

use numeric_id::{DenseIdMap, NumericId};
use rustc_hash::FxHasher;
use smallvec::SmallVec;

use crate::{
    action::{Bindings, ExecutionState, PredictedVals},
    common::{HashMap, Value},
    free_join::get_index_from_tableinfo,
    hash_index::{ColumnIndex, IndexBase, TupleIndex},
    offsets::{Offsets, SortedOffsetVector, Subset},
    pool::{Clear, Pooled},
    query::RuleSet,
    row_buffer::TaggedRowBuffer,
    table_spec::{ColumnId, Offset},
    OffsetRange, Pool, SubsetRef,
};

use super::{
    get_column_index_from_tableinfo,
    plan::{JoinStage, Plan},
    ActionId, AtomId, Database, HashColumnIndex, HashIndex, Variable,
};

enum DynamicIndex {
    Cached {
        intersect_outer: bool,
        table: HashIndex,
    },
    CachedColumn {
        intersect_outer: bool,
        table: HashColumnIndex,
    },
    Dynamic(TupleIndex),
    DynamicColumn(Rc<ColumnIndex>),
}

struct Prober {
    subset: Subset,
    pool: Pool<SortedOffsetVector>,
    ix: DynamicIndex,
}

impl Prober {
    fn get_subset(&self, key: &[Value]) -> Option<Subset> {
        match &self.ix {
            DynamicIndex::Cached {
                intersect_outer,
                table,
            } => {
                let mut sub = table.borrow().get_subset(key)?.to_owned(&self.pool);
                if *intersect_outer {
                    sub.intersect(self.subset.as_ref(), &self.pool);
                    if sub.is_empty() {
                        return None;
                    }
                }
                Some(sub)
            }
            DynamicIndex::CachedColumn {
                intersect_outer,
                table,
            } => {
                debug_assert_eq!(key.len(), 1);
                let mut sub = table.borrow().get_subset(&key[0])?.to_owned(&self.pool);
                if *intersect_outer {
                    sub.intersect(self.subset.as_ref(), &self.pool);
                    if sub.is_empty() {
                        return None;
                    }
                }
                Some(sub)
            }
            DynamicIndex::Dynamic(tab) => tab.get_subset(key).map(|x| x.to_owned(&self.pool)),
            DynamicIndex::DynamicColumn(tab) => {
                tab.get_subset(&key[0]).map(|x| x.to_owned(&self.pool))
            }
        }
    }
    fn for_each(&self, mut f: impl FnMut(&[Value], SubsetRef)) {
        match &self.ix {
            DynamicIndex::Cached {
                intersect_outer: true,
                table,
            } => table.borrow().for_each(|k, v| {
                let mut res = v.to_owned(&self.pool);
                res.intersect(self.subset.as_ref(), &self.pool);
                if !res.is_empty() {
                    f(k, res.as_ref())
                }
            }),
            DynamicIndex::Cached {
                intersect_outer: false,
                table,
            } => table.borrow().for_each(|k, v| f(k, v)),
            DynamicIndex::CachedColumn {
                intersect_outer: true,
                table,
            } => {
                table.borrow().for_each(|k, v| {
                    let mut res = v.to_owned(&self.pool);
                    res.intersect(self.subset.as_ref(), &self.pool);
                    if !res.is_empty() {
                        f(&[*k], res.as_ref())
                    }
                });
            }
            DynamicIndex::CachedColumn {
                intersect_outer: false,
                table,
            } => {
                table.borrow().for_each(|k, v| f(&[*k], v));
            }
            DynamicIndex::Dynamic(tab) => {
                tab.for_each(f);
            }
            DynamicIndex::DynamicColumn(tab) => tab.for_each(|k, v| {
                f(&[*k], v);
            }),
        }
    }

    fn len(&self) -> usize {
        match &self.ix {
            DynamicIndex::Cached { table, .. } => table.borrow().len(),
            DynamicIndex::CachedColumn { table, .. } => table.borrow().len(),
            DynamicIndex::Dynamic(tab) => tab.len(),
            DynamicIndex::DynamicColumn(tab) => tab.len(),
        }
    }
}

impl Database {
    pub fn run_rule_set(&mut self, rule_set: &RuleSet) -> bool {
        let mut preds = PredictedVals::default();
        let mut join_state = JoinState {
            db: self,
            preds: &mut preds,
            subsets: Default::default(),
            bindings: Default::default(),
            var_batches: Default::default(),
            index_cache: Default::default(),
        };
        for (plan, desc) in &rule_set.plans {
            let start = Instant::now();
            for (id, info) in plan.atoms.iter() {
                let table = join_state.db.get_table(info.table);
                join_state
                    .subsets
                    .insert(id, table.all(&join_state.db.pool_set));
            }
            join_state.run_plan(plan, rule_set, 0);
            join_state.subsets.clear();
            join_state.bindings.clear();
            let elapsed = start.elapsed();
            if elapsed > Duration::from_secs(1) {
                log::debug!("Rule {desc} took {elapsed:?}");
                log::debug!("Plan for {desc}: {plan:#?}");
            } else {
                log::trace!("Rule {desc} took {elapsed:?}");
            }
        }
        let mut batches = join_state.var_batches;
        let mut exec_state = ExecutionState {
            db: self,
            predicted: &mut preds,
        };
        // Run any remaining batches.
        for (action, ActionState { bindings, .. }) in batches.iter_mut() {
            exec_state.run_instrs(&rule_set.actions[action], bindings);
        }
        exec_state.merge_all()
    }
}

#[derive(Default)]
struct ActionState {
    n_runs: usize,
    bindings: Bindings,
}

struct JoinState<'a> {
    db: &'a mut Database,
    preds: &'a mut PredictedVals,
    subsets: DenseIdMap<AtomId, Subset>,
    bindings: DenseIdMap<Variable, Value>,
    var_batches: DenseIdMap<ActionId, ActionState>,
    index_cache: HashMap<(ColumnId, Subset), Rc<ColumnIndex>>,
}

impl<'a> JoinState<'a> {
    fn get_index(
        &mut self,
        plan: &Plan,
        atom: AtomId,
        cols: impl Iterator<Item = ColumnId>,
    ) -> Prober {
        let cols = SmallVec::<[ColumnId; 4]>::from_iter(cols);
        let subset = self.subsets.take(atom);

        let info = &mut self.db.tables[plan.atoms[atom].table];
        let all_cacheable = cols.iter().all(|col| {
            !info
                .spec
                .uncacheable_columns
                .get(*col)
                .copied()
                .unwrap_or(false)
        });
        let whole_table = info.table.all(&self.db.pool_set);
        let dyn_index =
            if all_cacheable && subset.is_dense() && whole_table.size() / 2 < subset.size() {
                // Skip intersecting with the subset if we are just looking at the
                // whole table.
                let intersect_outer =
                    !(whole_table.is_dense() && subset.bounds() == whole_table.bounds());
                // heuristic: if the subset we are scanning is somewhat
                // large _or_ it is most of the table, or we already have a cached
                // index for it, then return it.
                if cols.len() != 1 {
                    DynamicIndex::Cached {
                        intersect_outer,
                        table: get_index_from_tableinfo(info, &cols, &self.db.pool_set).clone(),
                    }
                } else {
                    DynamicIndex::CachedColumn {
                        intersect_outer,
                        table: get_column_index_from_tableinfo(info, cols[0], &self.db.pool_set)
                            .clone(),
                    }
                }
            } else if cols.len() != 1 {
                DynamicIndex::Dynamic(info.table.pivot(subset.as_ref(), &cols, &self.db.pool_set))
            } else {
                DynamicIndex::DynamicColumn(if subset.size() > 16 {
                    let mut hasher = FxHasher::default();
                    (&cols[0], &subset).hash(&mut hasher);
                    let hc = hasher.finish();

                    let pool_set = &self.db.pool_set;
                    let subset = &subset;
                    let (_, res) = self
                        .index_cache
                        .raw_entry_mut()
                        .from_hash(hc, |(col, sub)| *col == cols[0] && *sub == *subset)
                        .or_insert_with(|| {
                            (
                                (cols[0], subset.clone()),
                                Rc::new(info.table.pivot_col(subset.as_ref(), cols[0], pool_set)),
                            )
                        });
                    res.clone()
                } else {
                    Rc::new(
                        info.table
                            .pivot_col(subset.as_ref(), cols[0], &self.db.pool_set),
                    )
                })
            };
        Prober {
            subset,
            pool: self.db.pool_set.get_pool().clone(),
            ix: dyn_index,
        }
    }
    fn get_column_index(&mut self, plan: &Plan, atom: AtomId, col: ColumnId) -> Prober {
        self.get_index(plan, atom, iter::once(col))
    }
    fn run_plan(&mut self, plan: &Plan, rule_set: &RuleSet, cur: usize) {
        if cur >= plan.stages.len() {
            return;
        }
        // Helper macro (not its own method to appease the borrow checker).
        macro_rules! drain_updates {
            ($updates:expr) => {
                for mut update in $updates.drain(..) {
                    for (var, val) in update.bindings.drain(..) {
                        self.bindings.insert(var, val);
                    }
                    for (atom, subset) in update.refinements.drain(..) {
                        self.subsets.insert(atom, subset);
                    }
                    self.run_plan(plan, rule_set, cur + 1);
                }
            };
        }
        match &plan.stages[cur] {
            JoinStage::EvalConstraints { atom, subset, .. } => {
                if subset.is_empty() {
                    return;
                }
                let prev = self.subsets.take(*atom);
                self.subsets.insert(*atom, subset.clone());
                self.run_plan(plan, rule_set, cur + 1);
                self.subsets.insert(*atom, prev);
            }
            JoinStage::Intersect { var, scans } => match scans.as_slice() {
                [] => {}
                [a] if a.cs.is_empty() => {
                    if self.subsets[a.atom].is_empty() {
                        return;
                    }
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                    let prober = self.get_column_index(plan, a.atom, a.column);
                    prober.for_each(|val, x| {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                        update.push_binding(*var, val[0]);
                        let sub = x.to_owned(self.db.pool_set.get_pool());
                        update.refine_atom(a.atom, sub);
                        updates.push(update);
                        if updates.len() >= CHUNK_SIZE {
                            drain_updates!(updates);
                        }
                    });
                    drain_updates!(updates);
                    self.subsets.insert(a.atom, prober.subset);
                }
                [a] => {
                    if self.subsets[a.atom].is_empty() {
                        return;
                    }
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                    let prober = self.get_column_index(plan, a.atom, a.column);
                    prober.for_each(|val, x| {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                        update.push_binding(*var, val[0]);
                        let sub = self.db.tables[plan.atoms[a.atom].table].table.refine(
                            x.to_owned(self.db.pool_set.get_pool()),
                            &a.cs,
                            &self.db.pool_set,
                        );
                        if sub.is_empty() {
                            return;
                        }
                        update.refine_atom(a.atom, sub);
                        updates.push(update);
                        if updates.len() >= CHUNK_SIZE {
                            drain_updates!(updates);
                        }
                    });
                    drain_updates!(updates);
                    self.subsets.insert(a.atom, prober.subset);
                }
                [a, b] => {
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                    let a_prober = self.get_column_index(plan, a.atom, a.column);
                    let b_prober = self.get_column_index(plan, b.atom, b.column);

                    let ((smaller, smaller_scan), (larger, larger_scan)) =
                        if a_prober.len() < b_prober.len() {
                            ((&a_prober, a), (&b_prober, b))
                        } else {
                            ((&b_prober, b), (&a_prober, a))
                        };

                    let smaller_atom = smaller_scan.atom;
                    let larger_atom = larger_scan.atom;
                    smaller.for_each(|val, small_sub| {
                        if let Some(mut large_sub) = larger.get_subset(val) {
                            if !larger_scan.cs.is_empty() {
                                large_sub = self.db.tables[plan.atoms[larger_atom].table]
                                    .table
                                    .refine(large_sub, &larger_scan.cs, &self.db.pool_set);
                                if large_sub.is_empty() {
                                    return;
                                }
                            }
                            let small_sub = if smaller_scan.cs.is_empty() {
                                small_sub.to_owned(self.db.pool_set.get_pool())
                            } else {
                                let sub =
                                    self.db.tables[plan.atoms[smaller_atom].table].table.refine(
                                        small_sub.to_owned(self.db.pool_set.get_pool()),
                                        &smaller_scan.cs,
                                        &self.db.pool_set,
                                    );
                                if sub.is_empty() {
                                    return;
                                }
                                sub
                            };
                            let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                            update.push_binding(*var, val[0]);
                            update.refine_atom(smaller_atom, small_sub);
                            update.refine_atom(larger_atom, large_sub);
                            updates.push(update);
                            if updates.len() >= CHUNK_SIZE {
                                drain_updates!(updates);
                            }
                        }
                    });
                    drain_updates!(updates);

                    self.subsets.insert(a.atom, a_prober.subset);
                    self.subsets.insert(b.atom, b_prober.subset);
                }
                rest => {
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                    let mut smallest = 0;
                    let mut smallest_size = usize::MAX;
                    let mut probers = Vec::with_capacity(rest.len());
                    for (i, scan) in rest.iter().enumerate() {
                        let prober = self.get_column_index(plan, scan.atom, scan.column);
                        let size = prober.len();
                        if size < smallest_size {
                            smallest = i;
                            smallest_size = size;
                        }
                        probers.push(prober);
                    }

                    if smallest_size == 0 {
                        return;
                    }

                    // Smallest leads the scan
                    probers[smallest].for_each(|key, sub| {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                        update.push_binding(*var, key[0]);
                        for (i, scan) in rest.iter().enumerate() {
                            if i == smallest {
                                continue;
                            }
                            if let Some(mut sub) = probers[i].get_subset(key) {
                                if !rest[i].cs.is_empty() {
                                    sub = self.db.tables[plan.atoms[rest[i].atom].table]
                                        .table
                                        .refine(sub, &rest[i].cs, &self.db.pool_set);
                                    if sub.is_empty() {
                                        return;
                                    }
                                }
                                update.refine_atom(scan.atom, sub)
                            } else {
                                // Empty intersection.
                                return;
                            }
                        }
                        let main_spec = &rest[smallest];
                        let mut sub = sub.to_owned(self.db.pool_set.get_pool());
                        if !main_spec.cs.is_empty() {
                            sub = self.db.tables[plan.atoms[main_spec.atom].table]
                                .table
                                .refine(sub, &main_spec.cs, &self.db.pool_set);
                            if sub.is_empty() {
                                return;
                            }
                        }
                        update.refine_atom(main_spec.atom, sub);
                        updates.push(update);
                        if updates.len() >= CHUNK_SIZE {
                            drain_updates!(updates);
                        }
                    });
                    drain_updates!(updates);
                    for (spec, prober) in rest.iter().zip(probers.into_iter()) {
                        self.subsets.insert(spec.atom, prober.subset);
                    }
                }
            },
            JoinStage::FusedIntersect {
                cover,
                bind,
                to_intersect,
            } if to_intersect.is_empty() => {
                let cover_atom = cover.to_index.atom;
                if self.subsets[cover_atom].is_empty() {
                    return;
                }
                let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                let proj = SmallVec::<[ColumnId; 4]>::from_iter(bind.iter().map(|(col, _)| *col));
                let cover_subset = self.subsets.take(cover_atom);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len(), &self.db.pool_set);
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        cover_subset.as_ref(),
                        &proj,
                        cur,
                        CHUNK_SIZE,
                        &cover.constraints,
                        &mut buffer,
                    );
                    for (row, key) in buffer.iter_non_stale() {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                        update.refine_atom(
                            cover_atom,
                            Subset::Dense(OffsetRange::new(row, row.inc())),
                        );
                        // bind the values
                        for (i, (_, var)) in bind.iter().enumerate() {
                            update.push_binding(*var, key[i]);
                        }
                        updates.push(update);
                        if updates.len() >= CHUNK_SIZE {
                            drain_updates!(updates);
                        }
                    }
                    if let Some(next) = next {
                        cur = next;
                        continue;
                    }
                    break;
                }
                drain_updates!(updates);
                // Restore the subsets we swapped out.
                self.subsets.insert(cover_atom, cover_subset);
            }
            JoinStage::FusedIntersect {
                cover,
                bind,
                to_intersect,
            } => {
                let cover_atom = cover.to_index.atom;
                if self.subsets[cover_atom].is_empty() {
                    return;
                }
                let index_probers = to_intersect
                    .iter()
                    .enumerate()
                    .map(|(i, (spec, _))| {
                        (
                            i,
                            spec.to_index.atom,
                            self.get_index(
                                plan,
                                spec.to_index.atom,
                                spec.to_index.vars.iter().copied(),
                            ),
                        )
                    })
                    .collect::<SmallVec<[(usize, AtomId, Prober); 4]>>();
                let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();
                let proj = SmallVec::<[ColumnId; 4]>::from_iter(bind.iter().map(|(col, _)| *col));
                let cover_subset = self.subsets.take(cover_atom);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len(), &self.db.pool_set);
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        cover_subset.as_ref(),
                        &proj,
                        cur,
                        CHUNK_SIZE,
                        &cover.constraints,
                        &mut buffer,
                    );
                    'mid: for (row, key) in buffer.iter_non_stale() {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
                        update.refine_atom(
                            cover_atom,
                            Subset::Dense(OffsetRange::new(row, row.inc())),
                        );
                        // bind the values
                        for (i, (_, var)) in bind.iter().enumerate() {
                            update.push_binding(*var, key[i]);
                        }
                        // now probe each remaining indexes
                        for (i, atom, prober) in &index_probers {
                            // create a key: to_intersect indexes into the key from the cover
                            let index_cols = &to_intersect[*i].1;
                            let index_key = index_cols
                                .iter()
                                .map(|col| key[col.index()])
                                .collect::<SmallVec<[Value; 4]>>();
                            let Some(mut subset) = prober.get_subset(&index_key) else {
                                // There are no possible values for this subset
                                continue 'mid;
                            };
                            // apply any constraints needed in this scan.
                            let table_info = &self.db.tables[plan.atoms[*atom].table];
                            let cs = &to_intersect[*i].0.constraints;
                            if !cs.is_empty() {
                                subset = table_info.table.refine(subset, cs, &self.db.pool_set);
                            }
                            if subset.is_empty() {
                                // There are no possible values for this subset
                                continue 'mid;
                            }
                            update.refine_atom(*atom, subset);
                        }
                        updates.push(update);
                        if updates.len() >= CHUNK_SIZE {
                            drain_updates!(updates);
                        }
                    }
                    if let Some(next) = next {
                        cur = next;
                        continue;
                    }
                    break;
                }
                // TODO: special-case the scenario when the cover doesn't need
                // deduping (and hence we can do a straight scan: e.g. when the
                // cover is binding a superset of the primary key for the
                // table).
                drain_updates!(updates);
                // Restore the subsets we swapped out.
                self.subsets.insert(cover_atom, cover_subset);
                for (_, atom, prober) in index_probers {
                    self.subsets.insert(atom, prober.subset);
                }
            }
            JoinStage::RunInstrs { actions } => {
                let action_state = self.var_batches.get_or_default(*actions);
                let mut len = 0;
                action_state.n_runs += 1;
                for (var, val) in self.bindings.iter() {
                    let vals = action_state
                        .bindings
                        .get_or_insert(var, || self.db.pool_set.get());
                    vals.push(*val);
                    len = vals.len();
                }
                if len > VAR_BATCH_SIZE {
                    let mut state = ExecutionState {
                        db: self.db,
                        predicted: self.preds,
                    };
                    state.run_instrs(&rule_set.actions[*actions], &mut action_state.bindings);
                    action_state.bindings.clear();
                }
            }
        }
    }
}

#[derive(Default)]
pub(crate) struct FrameUpdate {
    bindings: Vec<(Variable, Value)>,
    refinements: Vec<(AtomId, Subset)>,
}

impl FrameUpdate {
    fn push_binding(&mut self, var: Variable, val: Value) {
        self.bindings.push((var, val));
    }

    fn refine_atom(&mut self, atom: AtomId, subset: Subset) {
        self.refinements.push((atom, subset));
    }
}

impl Clear for FrameUpdate {
    fn clear(&mut self) {
        self.bindings.clear();
        self.refinements.clear();
    }
    fn reuse(&self) -> bool {
        self.bindings.capacity() > 0 || self.refinements.capacity() > 0
    }
}

const CHUNK_SIZE: usize = 256;
const VAR_BATCH_SIZE: usize = 1024;

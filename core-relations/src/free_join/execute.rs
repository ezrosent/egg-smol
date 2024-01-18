//! Core free join execution.

use smallvec::SmallVec;

use crate::{
    action::{Bindings, ExecutionState, PredictedVals},
    common::{DenseIdMap, NumericId, Value},
    free_join::get_index_from_tableinfo,
    hash_index::{KeySet, PivotTable},
    offsets::{Offsets, Subset},
    pool::{Clear, Pooled},
    query::RuleSet,
    row_buffer::TaggedRowBuffer,
    table_spec::{ColumnId, Offset},
};

use super::{
    plan::{JoinStage, Plan},
    ActionId, AtomId, Database, HashIndex, Variable,
};

enum DynamicIndex {
    Cached(HashIndex),
    Dynamic(PivotTable),
}

struct Prober {
    subset: Subset,
    ix: DynamicIndex,
}

impl Prober {
    fn get_subset(&self, key: &[Value]) -> Option<Subset> {
        match &self.ix {
            DynamicIndex::Cached(ix) => {
                let mut sub = ix.borrow().get_subset(key)?.clone();
                sub.intersect(&self.subset);
                Some(sub)
            }
            DynamicIndex::Dynamic(tab) => tab.get_subset(key).cloned(),
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
        };
        for plan in &rule_set.plans {
            for (id, info) in plan.atoms.iter() {
                let table = join_state.db.get_table(info.table);
                join_state
                    .subsets
                    .insert(id, table.all(&join_state.db.pool_set));
            }
            join_state.run_plan(plan, rule_set, 0);
            join_state.subsets.clear();
            join_state.bindings.clear();
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
}

impl<'a> JoinState<'a> {
    fn get_index(
        &mut self,
        plan: &Plan,
        atom: AtomId,
        cols: impl Iterator<Item = ColumnId>,
    ) -> Prober {
        let cols = SmallVec::<[ColumnId; 4]>::from_iter(cols);
        let info = &mut self.db.tables[plan.atoms[atom].table];
        let all_cacheable = cols.iter().all(|col| {
            !info
                .spec
                .uncacheable_columns
                .get(*col)
                .copied()
                .unwrap_or(false)
        });
        let subset = self.subsets.take(atom);
        let dyn_index = if all_cacheable
            && (info.indexes.contains_key(&cols)
                || subset.size() > 512
                || info.table.all(&self.db.pool_set).size() / 2 < subset.size())
        {
            // heuristic: if the subset we are scanning is somewhat
            // large _or_ it is most of the table, or we already have a cached
            // index for it, then return it.
            DynamicIndex::Cached(get_index_from_tableinfo(info, &cols, &self.db.pool_set).clone())
        } else {
            DynamicIndex::Dynamic(info.table.pivot(&subset, &cols, &self.db.pool_set))
        };
        Prober {
            subset,
            ix: dyn_index,
        }
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
            // TODO: more specializations
            JoinStage::Intersect {
                cover,
                bind,
                to_intersect,
            } if to_intersect.is_empty() => {
                let cover_atom = cover.to_index.atom;
                if self.subsets[cover_atom].is_empty() {
                    return;
                }
                let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = self.db.pool_set.get();

                // NB: we skip the key_dedup phase here due to the overhead that
                // it adds. We should evaluate skipping it everywhere once we have more benchmarks.
                let proj = SmallVec::<[ColumnId; 4]>::from_iter(bind.iter().map(|(col, _)| *col));
                let cover_subset = self.subsets.take(cover_atom);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len(), &self.db.pool_set);
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        &cover_subset,
                        &proj,
                        cur,
                        CHUNK_SIZE,
                        &cover.constraints,
                        &mut buffer,
                    );
                    for (_, key) in buffer.iter_non_stale() {
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
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
            JoinStage::Intersect {
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
                let mut key_dedup = KeySet::new(bind.len(), &self.db.pool_set);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len(), &self.db.pool_set);
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        &cover_subset,
                        &proj,
                        cur,
                        CHUNK_SIZE,
                        &cover.constraints,
                        &mut buffer,
                    );
                    'mid: for (_, key) in buffer.iter_non_stale() {
                        if !key_dedup.insert(key) {
                            continue;
                        }
                        let mut update: Pooled<FrameUpdate> = self.db.pool_set.get();
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

const CHUNK_SIZE: usize = 512;
const VAR_BATCH_SIZE: usize = 1024;

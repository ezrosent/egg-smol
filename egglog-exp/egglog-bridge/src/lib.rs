//! An implementation of egglog-style queries on top of core-relations.
//!
//! This module translates a well-typed egglog-esque query into the abstractions
//! from the `core-relations` crate. The main higher-level functionality that it
//! implements are seminaive evaluation, default values, and merge functions.
//!
//! This crate is essentially involved in desugaring: it elaborates the encoding
//! of core egglog functionality, but it does not implement algorithms for
//! joins, union-finds, etc.

use std::{cell::RefCell, iter::once, rc::Rc, time::Instant};

use core_relations::{
    ColumnId, Constraint, CounterId, Database, DisplacedTable, DisplacedTableWithProvenance,
    ExternalFunction, ExternalFunctionId, MergeVal, Offset, PlanStrategy, PrimitiveId, Primitives,
    SortedWritesTable, TableId, TaggedRowBuffer, Value,
};
use indexmap::{map::Entry, IndexMap};
use numeric_id::{define_id, DenseIdMap, NumericId};
use proof_dag::RowProof;
use proof_spec::{cong_row, get_row_proof, ProofSpec, ProofSpecId};
use smallvec::SmallVec;

pub mod macros;
pub(crate) mod proof_dag;
pub(crate) mod proof_spec;
pub(crate) mod rule;
#[cfg(test)]
mod tests;

pub use rule::{Function, QueryEntry, RuleBuilder};
use thiserror::Error;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ColumnTy {
    Id,
    Primitive(PrimitiveId),
}

define_id!(pub RuleId, u32, "An egglog-style rule");
define_id!(pub FunctionId, u32, "An id representing an egglog function");
define_id!(pub(crate) Timestamp, u32, "An abstract timestamp used to track execution of egglog rules");
impl Timestamp {
    fn to_value(self) -> Value {
        Value::new(self.rep())
    }
}

/// The state associated with an egglog program.
pub struct EGraph {
    db: Database,
    uf_table: TableId,
    id_counter: CounterId,
    trace_counter: CounterId,
    next_ts: Timestamp,
    rules: DenseIdMap<RuleId, RuleInfo>,
    funcs: DenseIdMap<FunctionId, FunctionInfo>,
    proof_specs: DenseIdMap<ProofSpecId, Rc<ProofSpec>>,
    /// Side tables used to store proof information. We initialize these lazily
    /// as a proof object with a given number of parameters is added.
    trace_tables: IndexMap<usize /* arity */, TableId>,
    side_channel: Rc<RefCell<Option<Vec<Value>>>>,
    get_first_id: ExternalFunctionId,
    tracing: bool,
}

pub type Result<T> = std::result::Result<T, anyhow::Error>;

impl Default for EGraph {
    fn default() -> Self {
        let mut db = Database::new();
        let uf_table = db.add_table(DisplacedTable::default());
        EGraph::create_internal(db, uf_table, false)
    }
}

impl EGraph {
    /// Create a new EGraph with tracing (aka 'proofs') enabled.
    ///
    /// Execution of queries against a tracing-enabled EGgraph will be slower,
    /// but will annotate the egraph with annotations that can explain how rows
    /// came to appera.
    pub fn with_tracing() -> EGraph {
        let mut db = Database::new();
        let uf_table = db.add_table(DisplacedTableWithProvenance::default());
        EGraph::create_internal(db, uf_table, true)
    }

    fn create_internal(mut db: Database, uf_table: TableId, tracing: bool) -> EGraph {
        let id_counter = db.add_counter();
        let trace_counter = db.add_counter();
        let side_channel = Rc::new(RefCell::new(None));
        let get_first = GetFirstMatch {
            side_channel: side_channel.clone(),
        };
        let get_first_id = db.add_external_function(get_first);
        Self {
            db,
            uf_table,
            id_counter,
            trace_counter,
            next_ts: Timestamp::new(1),
            rules: Default::default(),
            funcs: Default::default(),
            proof_specs: Default::default(),
            trace_tables: Default::default(),
            side_channel,
            get_first_id,
            tracing,
        }
    }
    /// Get the underlying table of primitives for this EGraph.
    pub fn primitives_mut(&mut self) -> &mut Primitives {
        self.db.primitives_mut()
    }

    /// Generate a fresh id.
    pub fn fresh_id(&mut self) -> Value {
        Value::from_usize(self.db.inc_counter(self.id_counter))
    }

    /// Get the value populated by the `GetFirstMatch` external function and
    /// clear the side-channel state for that function.
    ///
    /// This is a lightweight way to pass information returned by a query.
    pub(crate) fn take_side_channel(&self) -> Option<Vec<Value>> {
        self.side_channel.borrow_mut().take()
    }

    /// Look up the canonical value for `val` in the union-find.
    ///
    /// If the value has never been inserted into the union-find, `val` is returned.
    pub fn get_canon(&self, val: Value) -> Value {
        let table = self.db.get_table(self.uf_table);
        let row = table.get_row(&[val], self.db.pool_set());
        row.map(|row| row.vals[1]).unwrap_or(val)
    }

    fn trace_table(&mut self, arity: usize) -> TableId {
        match self.trace_tables.entry(arity) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(v) => {
                let table = SortedWritesTable::new(
                    arity,
                    arity + 1,
                    None,
                    |_, _, _, _| false,
                    self.db.pool_set(),
                );

                let table_id = self.db.add_table(table);
                v.insert(table_id);
                table_id
            }
        }
    }

    /// Load the given values into the database.
    ///
    /// # Panics
    /// This method panics if the values do not match the arity of the function.
    ///
    /// NB: this is not an efficient interface for bulk loading. We should add
    /// one that allows us to pass through a series of RowBuffers before
    /// incrementing the timestamp.
    pub fn add_values(&mut self, values: impl IntoIterator<Item = (FunctionId, Vec<Value>)>) {
        self.add_values_with_desc("", values)
    }

    /// Load the given values into the database. If tracing is enabled, the
    /// proof rows will be tagged with "desc" as their proof.
    ///
    /// # Panics
    /// This method panics if the values do not match the arity of the function.
    ///
    /// NB: this is not an efficient interface for bulk loading. We should add
    /// one that allows us to pass through a series of RowBuffers before
    /// incrementing the timestamp.
    pub fn add_values_with_desc(
        &mut self,
        desc: &str,
        values: impl IntoIterator<Item = (FunctionId, Vec<Value>)>,
    ) {
        let mut extended_row = SmallVec::<[Value; 8]>::new();
        for (func, row) in values.into_iter() {
            let table_info = &self.funcs[func];
            let table_id = table_info.table;
            let proof_spec: Option<ProofSpec> = if self.tracing {
                Some(ProofSpec::Fiat {
                    func,
                    arity: table_info.schema.len(),
                    desc: desc.into(),
                })
            } else {
                None
            };
            let proof_id = proof_spec.map(|proof_spec| {
                let trace_table = self.trace_table(proof_spec.arity());
                let spec_id = self.proof_specs.push(proof_spec.into());
                extended_row.push(Value::new(spec_id.rep()));
                extended_row.extend_from_slice(&row);
                let proof_id = Value::from_usize(self.db.inc_counter(self.trace_counter));
                extended_row.push(proof_id);
                let table = self.db.get_table_mut(trace_table);
                table.stage_insert(&extended_row);
                extended_row.clear();
                proof_id
            });
            let table = self.db.get_table_mut(table_id);
            extended_row.extend_from_slice(&row);
            extended_row.push(self.next_ts.to_value());
            if let Some(proof) = proof_id {
                extended_row.push(proof);
            }
            table.stage_insert(&extended_row);
            extended_row.clear();
        }
        self.db.merge_all();
        self.next_ts = self.next_ts.inc();
        self.rebuild().unwrap();
    }

    pub fn approx_table_size(&mut self, table: FunctionId) -> usize {
        self.db.estimate_size(self.funcs[table].table, None)
    }

    pub fn table_size(&mut self, table: FunctionId) -> usize {
        self.db
            .get_table(self.funcs[table].table)
            .len(self.db.pool_set())
    }

    /// Generate a proof explaining why a given row is in the database.
    ///
    /// # Errors
    /// This method will return an error if tracing is not enabled, or if the row is not in the database.
    ///
    /// # Panics
    /// This method may panic if `key` does not match the arity of the function,
    /// or is otherwise malformed.
    pub fn explain_row(&mut self, func: FunctionId, key: &[Value]) -> Result<Rc<RowProof>> {
        #[derive(Error, Debug)]
        enum ProofReconstructionError {
            #[error("attempting to explain a row without tracing enabled. Try constructing with `EGraph::with_tracing`")]
            TracingNotEnabled,
            #[error("attempting to construct a proof for a row that is not in the database")]
            RowNotFound,
        }
        if !self.tracing {
            return Err(ProofReconstructionError::TracingNotEnabled.into());
        }
        let table = self.funcs[func].table;
        let row = self.db.get_table(table).get_row(key, self.db.pool_set());
        let Some(row) = row else {
            return Err(ProofReconstructionError::RowNotFound.into());
        };
        // No error case here: there shouldn't be any nullary tables.
        let proof = *row.vals.last().unwrap();
        Ok(get_row_proof(proof, self, &mut Default::default()))
    }

    /// Read the contents of the given function.
    ///
    /// Useful for debugging.
    pub fn dump_table(&self, table: FunctionId, mut f: impl FnMut(&[Value])) {
        let table = self.funcs[table].table;
        let imp = self.db.get_table(table);
        let truncate = if self.tracing { 2 } else { 1 };
        let all = imp.all(self.db.pool_set());
        let mut cur = Offset::new(0);
        let mut buf = TaggedRowBuffer::new(imp.spec().arity(), self.db.pool_set());
        while let Some(next) = imp.scan_bounded(all.as_ref(), cur, 500, &mut buf) {
            buf.iter_non_stale()
                .for_each(|(_, row)| f(&row[0..row.len() - truncate]));
            cur = next;
            buf.clear();
        }
        buf.iter_non_stale()
            .for_each(|(_, row)| f(&row[0..row.len() - truncate]));
    }

    /// Register a function in this EGraph.
    pub fn add_table(
        &mut self,
        schema: Vec<ColumnTy>,
        default: DefaultVal,
        merge: MergeFn,
        name: &str,
    ) -> FunctionId {
        assert!(
            !schema.is_empty(),
            "must have at least one column in schema"
        );
        let n_args = schema.len() - 1;
        let n_cols = if self.tracing {
            schema.len() + 2
        } else {
            schema.len() + 1
        };
        let uf_table = self.uf_table;
        let tracing = self.tracing;

        // This is a bit of a hack. We need to get the trace table before we
        // actually know next_table_id. If we call next_table_id too early, it
        // will be wrong.
        let trace_table = self.trace_table(
            ProofSpec::Cong {
                func: FunctionId::new(!0),
                arity: schema.len(),
            }
            .arity(),
        );
        let proof_ctr = self.trace_counter;
        let next_func_id = self.funcs.next_id();
        let cong_spec = ProofSpec::Cong {
            func: next_func_id,
            arity: schema.len(),
        };
        let proof_id = self.proof_specs.push(cong_spec.into());
        let table = match merge {
            MergeFn::UnionId => SortedWritesTable::new(
                n_args,
                n_cols,
                Some(ColumnId::from_usize(schema.len())),
                move |state, cur, new, out| {
                    let l = cur[n_args];
                    let r = new[n_args];
                    let next_ts = new[n_args + 1];
                    if l != r {
                        if tracing {
                            let cong_row = cong_row(proof_id, n_args, cur, new);
                            let res = state.predict_val(
                                trace_table,
                                &cong_row,
                                once(MergeVal::Counter(proof_ctr)),
                            );
                            let proof_val = *res.last().unwrap();
                            state.stage_insert(uf_table, &[l, r, next_ts, proof_val]);
                        } else {
                            state.stage_insert(uf_table, &[l, r, next_ts]);
                        }
                        out.extend_from_slice(new);
                        true
                    } else {
                        false
                    }
                },
                self.db.pool_set(),
            ),
            MergeFn::Table(merge_table) => {
                let id_counter = self.id_counter;
                SortedWritesTable::new(
                    n_args,
                    n_cols,
                    Some(ColumnId::from_usize(schema.len())),
                    move |state, cur, new, out| {
                        // We have F(x0, ..., xn, v1, t1) and F(x0, ..., xn, v2,
                        // t2) in the same table.
                        // F has a merge function given by T. (`merge_table`).
                        let l = cur[n_args];
                        let r = new[n_args];
                        let next_ts = new[n_args + 1];
                        if l == r {
                            // Merge functions should be idempotent: T(x,x)
                            // should eventually equal x. We short-circuit here.
                            return false;
                        }
                        // Look up T(v1, v2), giving us a new value v* (+ a
                        // timestamp that we ignore). We use the "predictions"
                        // API, which is only safe because we do not allow "raw
                        // primitives" in return position here.
                        let res = if tracing {
                            let cong_row = cong_row(proof_id, n_args, cur, new);
                            let res = state.predict_val(
                                trace_table,
                                &cong_row,
                                once(MergeVal::Counter(proof_ctr)),
                            );
                            let proof_val = *res.last().unwrap();
                            state.predict_val(
                                merge_table,
                                &[l, r],
                                [
                                    MergeVal::from(id_counter),
                                    MergeVal::from(next_ts),
                                    MergeVal::from(proof_val),
                                ]
                                .into_iter(),
                            )
                        } else {
                            state.predict_val(
                                merge_table,
                                &[l, r],
                                [MergeVal::from(id_counter), MergeVal::from(next_ts)].into_iter(),
                            )
                        };
                        debug_assert_eq!(res.len(), 2);
                        // If v* = v1, return with "no change".
                        if res[0] == l {
                            return false;
                        }
                        // Otherwise, build a new tuple F(x0, ..., xn, v*, t2).
                        out.extend_from_slice(&new[0..n_args]);
                        out.push(res[0]);
                        out.extend_from_slice(&new[n_args + 1..]);
                        true
                    },
                    self.db.pool_set(),
                )
            }
        };
        let table_id = self.db.add_table(table);
        let res = self.funcs.push(FunctionInfo {
            table: table_id,
            schema: schema.clone(),
            incremental_rebuild_rules: Default::default(),
            nonincremental_rebuild_rule: RuleId::new(!0),
            default_val: default,
            name: name.to_string(),
        });
        debug_assert_eq!(res, next_func_id);
        let incremental_rebuild_rules = self.incremental_rebuild_rules(res, &schema);
        let nonincremental_rebuild_rule = self.nonincremental_rebuild(res, &schema);
        let info = &mut self.funcs[res];
        info.incremental_rebuild_rules = incremental_rebuild_rules;
        info.nonincremental_rebuild_rule = nonincremental_rebuild_rule;
        res
    }

    /// Run the given rules, returning whether the database changed.
    ///
    /// If the given rules are malformed, this method can return an error.
    pub fn run_rules(&mut self, rules: &[RuleId]) -> Result<bool> {
        if !run_rules_impl(&mut self.db, &mut self.rules, rules, self.next_ts)? {
            return Ok(false);
        }
        self.rebuild()?;
        Ok(true)
    }

    fn rebuild(&mut self) -> Result<()> {
        let start = Instant::now();
        fn incremental_rebuild(uf_size: usize, table_size: usize) -> bool {
            uf_size <= (table_size / 8)
        }
        // The database changed. Rebuild. New entries should land after the given rules.
        self.next_ts = self.next_ts.inc();
        let mut changed = true;
        while changed {
            changed = false;
            // We need to iterate rebuilding to a fixed point. Future scans
            // should look only at the latest updates.
            self.next_ts = self.next_ts.inc();
            for (_, info) in self.funcs.iter_mut() {
                let last_rebuilt_at = self.rules[info.nonincremental_rebuild_rule].last_run_at;
                let table_size = self.db.estimate_size(info.table, None);
                let uf_size = self.db.estimate_size(
                    self.uf_table,
                    Some(Constraint::GeConst {
                        col: ColumnId::new(2),
                        val: last_rebuilt_at.to_value(),
                    }),
                );
                if incremental_rebuild(uf_size, table_size) {
                    marker_incremental_rebuild(|| -> Result<()> {
                        // Run each of the incremental rules serially.
                        //
                        // This is to avoid recanonicalizing the same row multiple
                        // times.
                        for rule in &info.incremental_rebuild_rules {
                            changed |= run_rules_impl(
                                &mut self.db,
                                &mut self.rules,
                                &[*rule],
                                self.next_ts,
                            )?;
                        }
                        // Reset the rule we did not run. These two should be equivalent.
                        self.rules[info.nonincremental_rebuild_rule].last_run_at = self.next_ts;
                        Ok(())
                    })?;
                } else {
                    marker_nonincremental_rebuild(|| -> Result<()> {
                        changed |= run_rules_impl(
                            &mut self.db,
                            &mut self.rules,
                            &[info.nonincremental_rebuild_rule],
                            self.next_ts,
                        )?;
                        for rule in &info.incremental_rebuild_rules {
                            self.rules[*rule].last_run_at = self.next_ts;
                        }
                        Ok(())
                    })?;
                }
            }
        }
        log::info!("rebuild took {:?}", start.elapsed());
        Ok(())
    }

    fn incremental_rebuild_rules(&mut self, table: FunctionId, schema: &[ColumnTy]) -> Vec<RuleId> {
        schema
            .iter()
            .enumerate()
            .filter_map(|(i, ty)| match ty {
                ColumnTy::Id => {
                    Some(self.incremental_rebuild_rule(table, schema, ColumnId::from_usize(i)))
                }
                ColumnTy::Primitive(_) => None,
            })
            .collect()
    }

    fn incremental_rebuild_rule(
        &mut self,
        table: FunctionId,
        schema: &[ColumnTy],
        col: ColumnId,
    ) -> RuleId {
        let table_id = self.funcs[table].table;
        let uf_table = self.uf_table;
        // Two atoms, one binding a whole tuple, one binding a displaced column
        let mut rb = self.new_query();
        rb.set_plan_strategy(PlanStrategy::MinCover);
        let mut vars = Vec::<QueryEntry>::with_capacity(schema.len());
        for ty in schema {
            vars.push(rb.new_var(*ty).into());
        }
        let canon_val = rb.new_var(ColumnTy::Id);
        rb.add_atom_with_timestamp(table_id, &vars);
        rb.add_atom_with_timestamp(uf_table, &[vars[col.index()].clone(), canon_val.into()]);
        rb.set_focus(1); // Set the uf atom as the sole focus.

        // Now canonicalize the entire row.
        let mut canon = Vec::<QueryEntry>::with_capacity(schema.len());
        for (i, (var, ty)) in vars.iter().zip(schema.iter()).enumerate() {
            canon.push(if i == col.index() {
                canon_val.into()
            } else if let ColumnTy::Id = ty {
                rb.lookup_uf(var.clone()).unwrap().into()
            } else {
                var.clone()
            })
        }

        // Remove the old row and insert the new one.
        rb.rebuild_row(table, &vars, &canon);
        rb.build_described(format!("incremental rebuild {table:?}, {col:?}"))
    }

    fn nonincremental_rebuild(&mut self, table: FunctionId, schema: &[ColumnTy]) -> RuleId {
        let mut rb = self.new_nonincremental_query();
        rb.set_plan_strategy(PlanStrategy::MinCover);
        let mut vars = Vec::<QueryEntry>::with_capacity(schema.len());
        for ty in schema {
            vars.push(rb.new_var(*ty).into());
        }
        rb.add_atom(Function::Table(table), &vars).unwrap();
        let mut lhs = SmallVec::<[QueryEntry; 4]>::new();
        let mut rhs = SmallVec::<[QueryEntry; 4]>::new();
        let mut canon = Vec::<QueryEntry>::with_capacity(schema.len());
        for (var, ty) in vars.iter().zip(schema.iter()) {
            canon.push(if let ColumnTy::Id = ty {
                lhs.push(var.clone());
                let canon_var = QueryEntry::from(rb.lookup_uf(var.clone()).unwrap());
                rhs.push(canon_var.clone());
                canon_var
            } else {
                var.clone()
            })
        }
        rb.check_for_update(&lhs, &rhs).unwrap();
        rb.rebuild_row(table, &vars, &canon);
        rb.build_described(format!("nonincremental rebuild {table:?}"))
    }
}

struct RuleInfo {
    last_run_at: Timestamp,
    query: rule::Query,
    desc: String,
}

struct FunctionInfo {
    table: TableId,
    schema: Vec<ColumnTy>,
    incremental_rebuild_rules: Vec<RuleId>,
    nonincremental_rebuild_rule: RuleId,
    default_val: DefaultVal,
    name: String,
}

impl FunctionInfo {
    fn ret_ty(&self) -> ColumnTy {
        self.schema.last().copied().unwrap()
    }
}

/// How defaults are computed for the given function.
pub enum DefaultVal {
    /// Generate a fresh UF id.
    FreshId,
    /// Stop executing the rule. If a lookup occurs in the body of a rule for a
    /// mapping not in a function, execution of that rule will stop. This is
    /// similar to placing the value in the left-hand side of the rule, but this
    /// time the lookup can depend on values bound in the right-hand-side.
    Fail,
    /// Insert a constant of some kind.
    Const(Value),
}

/// How to resolve FD conflicts for a table.
pub enum MergeFn {
    /// Use congruence to resolve FD conflicts.
    UnionId,
    /// The corresponding output is replaced with the mapping in a table.
    Table(TableId),
}

fn run_rules_impl(
    db: &mut Database,
    rule_info: &mut DenseIdMap<RuleId, RuleInfo>,
    rules: &[RuleId],
    next_ts: Timestamp,
) -> Result<bool> {
    let mut rsb = db.new_rule_set();
    for rule in rules {
        let info = &mut rule_info[*rule];
        info.query.add_rules(
            &mut rsb,
            Timestamp::new(0),
            info.last_run_at,
            next_ts,
            &info.desc,
        )?;
        info.last_run_at = next_ts;
    }
    let ruleset = rsb.build();
    Ok(db.run_rule_set(&ruleset))
}

// These markers are just used to make it easy to distinguish time spent in
// incremental vs. nonincremental rebuilds in time-based profiles.

#[inline(never)]
fn marker_incremental_rebuild<R>(f: impl FnOnce() -> R) -> R {
    f()
}

#[inline(never)]
fn marker_nonincremental_rebuild<R>(f: impl FnOnce() -> R) -> R {
    f()
}

/// An external function used to grab a value out of the database matching a
/// particular query.
pub(crate) struct GetFirstMatch {
    pub(crate) side_channel: Rc<RefCell<Option<Vec<Value>>>>,
}

impl ExternalFunction for GetFirstMatch {
    fn invoke(&self, _: &mut core_relations::ExecutionState, args: &[Value]) -> Option<Value> {
        if self.side_channel.borrow().is_some() {
            return None;
        }
        *self.side_channel.borrow_mut() = Some(args.to_vec());
        Some(Value::new(0))
    }
}

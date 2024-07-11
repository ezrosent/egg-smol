//! APIs for building egglog rules.
//!
//! Egglog rules are ultimately just (sets of) `core-relations` rules
//! parameterized by a range of timestamps used as constraints during seminaive
//! evaluation.

use std::cmp::Ordering;
use std::iter;

use anyhow::Context;
use core_relations::{
    ColumnId, Constraint, CounterId, PlanStrategy, PrimitiveFunctionId, QueryBuilder,
    RuleBuilder as CoreRuleBuilder, RuleSetBuilder, TableId, Value, WriteVal,
};
use numeric_id::{define_id, DenseIdMap, NumericId};
use smallvec::SmallVec;
use thiserror::Error;

use crate::{
    proof_spec::{InsertKind, Insertable, ProofBuilder},
    ColumnTy, DefaultVal, EGraph, FunctionId, Result, RuleId, RuleInfo, Timestamp,
};

define_id!(pub Variable, u32, "A variable in an egglog query");
pub(crate) type DstVar = core_relations::QueryEntry;

#[derive(Debug, Error)]
enum RuleBuilderError {
    #[error("type mismatch: expected {expected:?}, got {got:?}")]
    TypeMismatch { expected: ColumnTy, got: ColumnTy },
    #[error("arity mismatch: expected {expected:?}, got {got:?}")]
    ArityMismatch { expected: usize, got: usize },
}

struct VarInfo {
    ty: ColumnTy,
}

#[derive(Clone, Debug)]
pub enum QueryEntry {
    Var {
        id: Variable,
        name: Option<Box<str>>,
    },
    Const(Value),
}

impl QueryEntry {
    /// Get the variable associated with this entry, panicking if it isn't a
    /// variable.
    pub(crate) fn var(&self) -> Variable {
        match self {
            QueryEntry::Var { id, .. } => *id,
            QueryEntry::Const(_) => panic!("expected variable, found constant"),
        }
    }

    pub(crate) fn render(&self) -> String {
        match self {
            QueryEntry::Var { name, id } => name
                .as_ref()
                .map(|x| x.to_string())
                .unwrap_or_else(|| format!("v{id:?}")),
            QueryEntry::Const(c) => format!("c{c:?}"),
        }
    }
}

impl From<Variable> for QueryEntry {
    fn from(id: Variable) -> Self {
        QueryEntry::Var { id, name: None }
    }
}

impl From<Value> for QueryEntry {
    fn from(v: Value) -> Self {
        QueryEntry::Const(v)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Function {
    Table(FunctionId),
    Prim(PrimitiveFunctionId),
}

impl From<FunctionId> for Function {
    fn from(f: FunctionId) -> Self {
        Function::Table(f)
    }
}

impl From<PrimitiveFunctionId> for Function {
    fn from(f: PrimitiveFunctionId) -> Self {
        Function::Prim(f)
    }
}

type BuildRuleCallback = Box<dyn Fn(&mut Bindings, &mut CoreRuleBuilder) -> Result<()>>;

pub(crate) struct Query {
    uf_table: TableId,
    id_counter: CounterId,
    tracing: bool,
    vars: DenseIdMap<Variable, VarInfo>,
    /// The current proofs that are in scope.
    atom_proofs: Vec<Variable>,
    atoms: Vec<(TableId, Vec<QueryEntry>)>,
    /// The builders for queries in this module essentially wrap the lower-level
    /// builders from the `core_relations` crate. A single egglog rule can turn
    /// into N core-relations rules. The code is structured by constructing a
    /// series of callbacks that will iteratively build up a low-level rule that
    /// looks like the high-level rule, passing along an environment that keeps
    /// track of the mappings between low and high-level variables.
    add_rule: Vec<BuildRuleCallback>,
    /// If set, execute a single rule (rather than O(atoms.len()) rules) during
    /// seminaive, with the given atom as the focus.
    sole_focus: Option<usize>,
    seminaive: bool,
    plan_strategy: PlanStrategy,
}

pub struct RuleBuilder<'a> {
    egraph: &'a mut EGraph,
    proof_builder: ProofBuilder,
    query: Query,
}

impl EGraph {
    pub fn new_query_described(&mut self, desc: &str) -> RuleBuilder {
        let uf_table = self.uf_table;
        let id_counter = self.id_counter;
        let tracing = self.tracing;
        RuleBuilder {
            egraph: self,
            proof_builder: ProofBuilder::new(desc.to_string()),
            query: Query {
                uf_table,
                id_counter,
                tracing,
                seminaive: true,
                sole_focus: None,
                atom_proofs: Default::default(),
                vars: Default::default(),
                atoms: Default::default(),
                add_rule: Default::default(),
                plan_strategy: Default::default(),
            },
        }
    }
    pub fn new_query(&mut self) -> RuleBuilder {
        self.new_query_described("")
    }

    pub(crate) fn new_nonincremental_query(&mut self) -> RuleBuilder {
        let mut res = self.new_query();
        res.query.seminaive = false;
        res
    }
}

impl RuleBuilder<'_> {
    fn add_callback(
        &mut self,
        cb: impl Fn(&mut Bindings, &mut CoreRuleBuilder) -> Result<()> + 'static,
    ) {
        self.query.add_rule.push(Box::new(cb));
    }

    /// Access the underlying egraph within the builder.
    pub(crate) fn egraph(&self) -> &EGraph {
        self.egraph
    }

    pub(crate) fn set_plan_strategy(&mut self, strategy: PlanStrategy) {
        self.query.plan_strategy = strategy;
    }

    /// Get the canonical value of an id in the union-find. An internal-only
    /// routine used to implement rebuilding.
    ///
    /// Note, calling this with a non-Id entry can cause errors at rule runtime
    /// (The derived rules will not compile).
    pub(crate) fn lookup_uf(&mut self, entry: QueryEntry) -> Result<Variable> {
        let res = self.new_var(ColumnTy::Id);
        let uf_table = self.query.uf_table;
        self.assert_has_ty(&entry, ColumnTy::Id)
            .context("lookup_uf: ")?;
        self.add_callback(move |inner, rb| {
            let entry = inner.convert(&entry);
            let res_inner = rb.lookup_with_default(uf_table, &[entry], entry, ColumnId::new(1))?;
            inner.mapping.insert(res, res_inner.into());
            Ok(())
        });
        Ok(res)
    }

    /// A low-level routine used in rebuilding. Halts execution if `lhs` and
    /// `rhs` are equal (pointwise).
    ///
    /// Note, calling this with invalid arguments (e.g. different lengths for
    /// `lhs` and `rhs`) can cause errors at rule runtime.
    pub(crate) fn check_for_update(
        &mut self,
        lhs: &[QueryEntry],
        rhs: &[QueryEntry],
    ) -> Result<()> {
        let lhs = SmallVec::<[QueryEntry; 4]>::from_iter(lhs.iter().cloned());
        let rhs = SmallVec::<[QueryEntry; 4]>::from_iter(rhs.iter().cloned());
        if lhs.len() != rhs.len() {
            return Err(RuleBuilderError::ArityMismatch {
                expected: lhs.len(),
                got: rhs.len(),
            }
            .into());
        }
        lhs.iter().zip(rhs.iter()).try_for_each(|(l, r)| {
            self.assert_same_ty(l, r).with_context(|| {
                format!("check_for_update: {lhs:?} and {rhs:?}, mismatch between {l:?} and {r:?}")
            })
        })?;

        self.add_callback(move |inner, rb| {
            let lhs = inner.convert_all(&lhs);
            let rhs = inner.convert_all(&rhs);
            rb.assert_any_ne(&lhs, &rhs).context("check_for_update")
        });
        Ok(())
    }

    fn assert_same_ty(
        &self,
        l: &QueryEntry,
        r: &QueryEntry,
    ) -> std::result::Result<(), RuleBuilderError> {
        match (l, r) {
            (QueryEntry::Var { id: v1, .. }, QueryEntry::Var { id: v2, .. }) => {
                let ty1 = self.query.vars[*v1].ty;
                let ty2 = self.query.vars[*v2].ty;
                if ty1 != ty2 {
                    return Err(RuleBuilderError::TypeMismatch {
                        expected: ty1,
                        got: ty2,
                    });
                }
            }
            // constants are untyped.
            (QueryEntry::Const(_), QueryEntry::Const(_))
            | (QueryEntry::Var { .. }, QueryEntry::Const(_))
            | (QueryEntry::Const(_), QueryEntry::Var { .. }) => {}
        }
        Ok(())
    }

    fn assert_has_ty(
        &self,
        entry: &QueryEntry,
        ty: ColumnTy,
    ) -> std::result::Result<(), RuleBuilderError> {
        if let QueryEntry::Var { id: v, .. } = entry {
            let var_ty = self.query.vars[*v].ty;
            if var_ty != ty {
                return Err(RuleBuilderError::TypeMismatch {
                    expected: var_ty,
                    got: ty,
                });
            }
        }
        Ok(())
    }

    /// Register the given rule with the egraph.
    pub fn build(self) -> RuleId {
        self.build_described("")
    }

    pub(crate) fn set_focus(&mut self, focus: usize) {
        self.query.sole_focus = Some(focus);
    }

    /// Register the given rule with the egraph.
    ///
    /// Include a string describing the rule for debugging purposes.
    pub fn build_described(mut self, msg: impl Into<String>) -> RuleId {
        if self.query.atoms.len() == 1 {
            self.query.plan_strategy = PlanStrategy::MinCover;
        }
        self.egraph.rules.push(RuleInfo {
            last_run_at: Timestamp::new(0),
            query: self.query,
            desc: msg.into(),
        })
    }

    /// Bind a new variable of the given type in the query.
    pub fn new_var(&mut self, ty: ColumnTy) -> Variable {
        self.query.vars.push(VarInfo { ty })
    }

    /// Bind a new variable of the given type in the query.
    ///
    /// This method attaches the given name to the [`QueryEntry`], which can
    /// make debugging easier.
    pub fn new_var_named(&mut self, ty: ColumnTy, name: &str) -> QueryEntry {
        let id = self.new_var(ty);
        QueryEntry::Var {
            id,
            name: Some(name.into()),
        }
    }

    pub(crate) fn add_atom_with_timestamp(&mut self, table: TableId, entries: &[QueryEntry]) {
        let mut atom = entries.to_vec();
        atom.push(self.new_var(ColumnTy::Id).into());
        if self.egraph.tracing {
            let proof_var = self.new_var(ColumnTy::Id);
            self.proof_builder.add_lhs(entries, proof_var);
            self.query.atom_proofs.push(proof_var);
            atom.push(proof_var.into());
        }
        self.query.atoms.push((table, atom));
    }

    /// Add the given atom to query. As elsewhere in the crate, the last
    /// argument is the "return value" of the function.
    pub fn add_atom(&mut self, func: Function, entries: &[QueryEntry]) -> Result<()> {
        match func {
            Function::Table(func) => {
                let schema = &self.egraph.funcs[func].schema;
                if schema.len() != entries.len() {
                    return Err(anyhow::Error::from(RuleBuilderError::ArityMismatch {
                        expected: schema.len(),
                        got: entries.len(),
                    }))
                    .with_context(|| {
                        format!("add_atom: mismatch between {entries:?} and {schema:?}")
                    });
                }
                entries
                    .iter()
                    .zip(schema.iter())
                    .try_for_each(|(entry, ty)| {
                        self.assert_has_ty(entry, *ty).with_context(|| {
                            format!("add_atom: mismatch between {entry:?} and {ty:?}")
                        })
                    })?;
                self.add_atom_with_timestamp(self.egraph.funcs[func].table, entries);
                Ok(())
            }
            Function::Prim(p) => {
                // Primitives on the LHS side of a rule turn into a call to a
                // primitive, along with an assertion that the result equals the
                // return value.
                let entries = SmallVec::<[_; 4]>::from_iter(entries.iter().cloned());
                let prim_schema = self.egraph.db.primitives().get_schema(p);
                if prim_schema.args.len() + 1 != entries.len() {
                    return Err(anyhow::Error::from(RuleBuilderError::ArityMismatch {
                        expected: prim_schema.args.len(),
                        got: entries.len(),
                    }))
                    .with_context(|| {
                        format!(
                            "add_atom/primitive: mismatch between {entries:?} and {:?}",
                            prim_schema.args
                        )
                    });
                }
                entries
                    .iter()
                    .zip(prim_schema.args.iter().chain(iter::once(&prim_schema.ret)))
                    .try_for_each(|(entry, ty)| {
                        self.assert_has_ty(entry, ColumnTy::Primitive(*ty))
                            .with_context(|| {
                                format!("add_atom/primitive: mismatch between {entry:?} and {ty:?}")
                            })
                    })?;

                self.query.add_rule.push(Box::new(move |inner, rb| {
                    let mut dst_vars = inner.convert_all(&entries);
                    let expected = dst_vars.pop().expect("must specify a return value");
                    let var = rb.prim(p, &dst_vars)?;
                    rb.assert_eq(var.into(), expected);
                    Ok(())
                }));
                Ok(())
            }
        }
    }

    /// Look up the value of a function in the database. If the value is not
    /// present, the configured default for the function is used.
    pub fn lookup(&mut self, func: Function, entries: &[QueryEntry]) -> Variable {
        let entries = entries.to_vec();
        let val_col = ColumnId::from_usize(entries.len());
        let (res, cb): (Variable, BuildRuleCallback) = match func {
            Function::Table(func) => {
                let info = &self.egraph.funcs[func];
                let res = self.query.vars.push(VarInfo { ty: info.ret_ty() });
                let table = info.table;
                let id_counter = self.query.id_counter;
                (
                    res,
                    match info.default_val {
                        DefaultVal::Const(_) | DefaultVal::FreshId => {
                            let wv: WriteVal = match &info.default_val {
                                DefaultVal::Const(c) => (*c).into(),
                                DefaultVal::FreshId => id_counter.into(),
                                _ => unreachable!(),
                            };
                            if self.egraph.tracing {
                                let prf_wv = WriteVal::from(self.egraph.trace_counter);
                                let prf = self.new_var(ColumnTy::Id);
                                let ts_var = self.new_var(ColumnTy::Id);
                                let mut insert_entries = entries.clone();
                                insert_entries.push(res.into());
                                let add_proof = self.proof_builder.set(
                                    Insertable::Func(func),
                                    insert_entries,
                                    prf,
                                    InsertKind::Lookup {
                                        ts_var: ts_var.into(),
                                    },
                                    self.egraph,
                                );
                                Box::new(move |inner, rb| {
                                    let dst_vars = inner.convert_all(&entries);
                                    // TODO: support projecting out multiple
                                    // destination columns. This is pretty
                                    // inefficient.
                                    let var = rb.lookup_or_insert(
                                        table,
                                        &dst_vars,
                                        &[wv, inner.next_ts.to_value().into(), prf_wv],
                                        val_col,
                                    )?;
                                    let ts = rb.lookup_or_insert(
                                        table,
                                        &dst_vars,
                                        &[wv, inner.next_ts.to_value().into(), prf_wv],
                                        ColumnId::from_usize(dst_vars.len() + 1),
                                    )?;
                                    let proof = rb.lookup_or_insert(
                                        table,
                                        &dst_vars,
                                        &[wv, inner.next_ts.to_value().into(), prf_wv],
                                        ColumnId::from_usize(dst_vars.len() + 2),
                                    )?;
                                    inner.mapping.insert(prf, proof.into());
                                    inner.mapping.insert(res, var.into());
                                    inner.mapping.insert(ts_var, ts.into());
                                    add_proof(inner, rb)?;
                                    Ok(())
                                })
                            } else {
                                Box::new(move |inner, rb| {
                                    let dst_vars = inner.convert_all(&entries);
                                    let var = rb.lookup_or_insert(
                                        table,
                                        &dst_vars,
                                        &[wv, inner.next_ts.to_value().into()],
                                        val_col,
                                    )?;
                                    inner.mapping.insert(res, var.into());
                                    Ok(())
                                })
                            }
                        }
                        DefaultVal::Fail => {
                            if self.egraph.tracing {
                                let prf = self.new_var(ColumnTy::Id);
                                self.proof_builder.add_lhs(&entries, prf);
                                Box::new(move |inner, rb| {
                                    let dst_vars = inner.convert_all(&entries);
                                    let var = rb.lookup(table, &dst_vars, val_col)?;
                                    let proof = rb.lookup(
                                        table,
                                        &dst_vars,
                                        ColumnId::from_usize(dst_vars.len() + 2),
                                    )?;
                                    inner.mapping.insert(res, var.into());
                                    inner.mapping.insert(prf, proof.into());
                                    Ok(())
                                })
                            } else {
                                Box::new(move |inner, rb| {
                                    let dst_vars = inner.convert_all(&entries);
                                    let var = rb.lookup(table, &dst_vars, val_col)?;
                                    inner.mapping.insert(res, var.into());
                                    Ok(())
                                })
                            }
                        }
                    },
                )
            }
            Function::Prim(p) => {
                let ret = self.egraph.db.primitives().get_schema(p).ret;
                let res = self.query.vars.push(VarInfo {
                    ty: ColumnTy::Primitive(ret),
                });
                (
                    res,
                    Box::new(move |inner, rb| {
                        let dst_vars = inner.convert_all(&entries);
                        let var = rb.prim(p, &dst_vars)?;
                        inner.mapping.insert(res, var.into());
                        Ok(())
                    }),
                )
            }
        };
        self.query.add_rule.push(cb);
        res
    }

    /// Merge the two values in the union-find.
    pub fn union(&mut self, l: QueryEntry, r: QueryEntry) {
        let cb: BuildRuleCallback = if self.query.tracing {
            let proof_var = self.new_var(ColumnTy::Id);
            let add_proof = self.proof_builder.set(
                Insertable::UnionFind,
                [l.clone(), r.clone()].to_vec(),
                proof_var,
                InsertKind::Insert,
                self.egraph,
            );
            Box::new(move |inner, rb| {
                let l = inner.convert(&l);
                let r = inner.convert(&r);
                add_proof(inner, rb)?;
                let proof = inner.mapping[proof_var];
                rb.insert(
                    inner.uf_table,
                    &[l, r, inner.next_ts.to_value().into(), proof],
                )
                .context("union")
            })
        } else {
            Box::new(move |inner, rb| {
                let l = inner.convert(&l);
                let r = inner.convert(&r);
                rb.insert(inner.uf_table, &[l, r, inner.next_ts.to_value().into()])
                    .context("union")
            })
        };
        self.query.add_rule.push(cb);
    }

    /// This method is equivalent to `remove(table, before); set(table, after)`
    /// when tracing/proofs aren't enabled. When proofs are enabled, it
    /// creates a proof term specialized for equality.
    ///
    /// This allows us to reconstruct proofs lazily from the UF, rather than
    /// running the proof generation algorithm eagerly as we query the table.
    /// Proof generation is a relatively expensive operation, and we'd prefer to
    /// avoid doing it on every union-find lookup.
    pub(crate) fn rebuild_row(
        &mut self,
        func: FunctionId,
        before: &[QueryEntry],
        after: &[QueryEntry],
    ) {
        assert_eq!(before.len(), after.len());
        self.remove(func, &before[..before.len() - 1]);
        if !self.egraph.tracing {
            self.set(func, after);
            return;
        }
        let table = self.egraph.funcs[func].table;
        let proof_var = self.new_var(ColumnTy::Id);
        let add_proof =
            self.proof_builder
                .rebuild_proof(func, before, after, proof_var, self.egraph);
        let after = SmallVec::<[_; 4]>::from_iter(after.iter().cloned());
        self.query.add_rule.push(Box::new(move |inner, rb| {
            add_proof(inner, rb)?;
            let mut dst_vars = inner.convert_all(&after);
            dst_vars.push(inner.next_ts.to_value().into());
            dst_vars.push(inner.mapping[proof_var]);
            rb.insert(table, &dst_vars).context("rebuild_row")
        }));
    }

    /// Set the value of a function in the database.
    pub fn set(&mut self, func: FunctionId, entries: &[QueryEntry]) {
        let table = self.egraph.funcs[func].table;
        let entries = entries.to_vec();
        let cb: BuildRuleCallback = if self.egraph.tracing {
            let proof_var = self.new_var(ColumnTy::Id);
            let add_proof = self.proof_builder.set(
                Insertable::Func(func),
                entries.to_vec(),
                proof_var,
                InsertKind::Insert,
                self.egraph,
            );
            Box::new(move |inner, rb| {
                add_proof(inner, rb)?;
                let mut dst_vars = inner.convert_all(&entries);
                dst_vars.push(inner.next_ts.to_value().into());
                dst_vars.push(inner.mapping[proof_var]);
                rb.insert(table, &dst_vars).context("set")
            })
        } else {
            Box::new(move |inner, rb| {
                let mut dst_vars = inner.convert_all(&entries);
                dst_vars.push(inner.next_ts.to_value().into());
                rb.insert(table, &dst_vars).context("set")
            })
        };
        self.query.add_rule.push(cb);
    }

    /// Remove the value of a function from the database.
    pub fn remove(&mut self, table: FunctionId, entries: &[QueryEntry]) {
        let table = self.egraph.funcs[table].table;
        let entries = entries.to_vec();
        let cb: BuildRuleCallback = Box::new(move |inner, rb| {
            let dst_vars = inner.convert_all(&entries);
            rb.remove(table, &dst_vars).context("remove")
        });
        self.query.add_rule.push(cb);
    }
}

impl Query {
    fn query_state<'a, 'outer>(
        &self,
        rsb: &'a mut RuleSetBuilder<'outer>,
        next_ts: Timestamp,
    ) -> (QueryBuilder<'outer, 'a>, Bindings) {
        let mut qb = rsb.new_query();
        qb.set_plan_strategy(self.plan_strategy);
        let mut inner = Bindings {
            uf_table: self.uf_table,
            next_ts,
            mapping: Default::default(),
        };
        for (var, _) in self.vars.iter() {
            inner.mapping.insert(var, DstVar::Var(qb.new_var()));
        }
        (qb, inner)
    }

    fn run_rules_and_build(&self, qb: QueryBuilder, mut inner: Bindings, desc: &str) -> Result<()> {
        let mut rb = qb.rules();
        self.add_rule
            .iter()
            .try_for_each(|f| f(&mut inner, &mut rb))?;
        rb.build_with_description(desc);
        Ok(())
    }

    /// Translate the egglog query into a (set of) queries against the database.
    ///
    /// The timestamp values are used to guide seminaive evaluation. The query
    /// is taken to have run against the database values between start_ts and
    /// mid_ts (half-open), but the database (now) contains values up to
    /// next_ts.
    pub(crate) fn add_rules(
        &self,
        rsb: &mut RuleSetBuilder,
        start_ts: Timestamp,
        mid_ts: Timestamp,
        next_ts: Timestamp,
        desc: &str,
    ) -> Result<()> {
        fn get_ts_col(atom: &[QueryEntry], tracing: bool) -> ColumnId {
            if tracing {
                ColumnId::from_usize(atom.len() - 2)
            } else {
                ColumnId::from_usize(atom.len() - 1)
            }
        }
        // For N atoms, we create N queries for seminaive evaluation.
        if !self.seminaive {
            let (mut qb, inner) = self.query_state(rsb, next_ts);
            for (table, entries) in &self.atoms {
                let dst_vars = inner.convert_all(entries);
                qb.add_atom(*table, &dst_vars, &[])?;
            }
            return self.run_rules_and_build(qb, inner, desc);
        }
        if let Some(focus_atom) = self.sole_focus {
            let (mut qb, inner) = self.query_state(rsb, next_ts);
            for (i, (table, entries)) in self.atoms.iter().enumerate() {
                let dst_vars = inner.convert_all(entries);
                let ts_range = if i == focus_atom {
                    mid_ts..next_ts
                } else {
                    start_ts..next_ts
                };
                if ts_range.start == ts_range.end {
                    // Empty timestamp range. This query will not run.
                    return Ok(());
                }
                let ts_col = get_ts_col(entries, self.tracing);
                qb.add_atom(
                    *table,
                    &dst_vars,
                    &[
                        Constraint::GeConst {
                            col: ts_col,
                            val: ts_range.start.to_value(),
                        },
                        Constraint::LtConst {
                            col: ts_col,
                            val: ts_range.end.to_value(),
                        },
                    ],
                )?;
            }
            return self.run_rules_and_build(
                qb,
                inner,
                &format!("{desc}-atom({focus_atom})[{start_ts:?},{mid_ts:?},{next_ts:?}]"),
            );
        }
        'outer: for focus_atom in 0..self.atoms.len() {
            let (mut qb, inner) = self.query_state(rsb, next_ts);
            for (i, (table, entries)) in self.atoms.iter().enumerate() {
                let dst_vars = inner.convert_all(entries);
                let ts_range = match focus_atom.cmp(&i) {
                    Ordering::Less => start_ts..next_ts,
                    Ordering::Equal => mid_ts..next_ts,
                    Ordering::Greater => start_ts..mid_ts,
                };
                if ts_range.start == ts_range.end {
                    // Empty timestamp range. This query will not run.
                    continue 'outer;
                }
                let ts_col = get_ts_col(entries, self.tracing);
                qb.add_atom(
                    *table,
                    &dst_vars,
                    &[
                        Constraint::GeConst {
                            col: ts_col,
                            val: ts_range.start.to_value(),
                        },
                        Constraint::LtConst {
                            col: ts_col,
                            val: ts_range.end.to_value(),
                        },
                    ],
                )?;
            }
            self.run_rules_and_build(
                qb,
                inner,
                &format!("{desc}-atom({focus_atom})[{start_ts:?},{mid_ts:?},{next_ts:?}]"),
            )?;
        }
        Ok(())
    }
}

/// State that is used during query execution to translate variabes in egglog
/// rules into variables for core-relations rules.
pub(crate) struct Bindings {
    uf_table: TableId,
    pub(crate) next_ts: Timestamp,
    pub(crate) mapping: DenseIdMap<Variable, DstVar>,
}

impl Bindings {
    pub(crate) fn convert(&self, entry: &QueryEntry) -> DstVar {
        match entry {
            QueryEntry::Var { id: v, .. } => self.mapping[*v],
            QueryEntry::Const(c) => DstVar::Const(*c),
        }
    }
    pub(crate) fn convert_all(&self, entries: &[QueryEntry]) -> SmallVec<[DstVar; 4]> {
        entries.iter().map(|e| self.convert(e)).collect()
    }
}

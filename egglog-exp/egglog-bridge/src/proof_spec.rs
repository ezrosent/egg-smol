use std::{
    collections::{HashMap, HashSet},
    iter,
    rc::Rc,
};

use core_relations::{
    ColumnId, DisplacedTableWithProvenance, PrimitivePrinter, ProofReason as UfProofReason,
    ProofStep, RuleBuilder, Value,
};
use indexmap::IndexSet;
use numeric_id::{define_id, NumericId};

use crate::{
    rule::{Bindings, DstVar, Variable},
    term_proof_dag::{EqProof, TermProof, TermValue},
    ColumnTy, EGraph, FunctionId, QueryEntry, Result,
};

define_id!(pub(crate) ReasonSpecId, u32, "A unique identifier for the step in a proof.");

/// Reasons provide extra provenance information accompanying a term being
/// instantiated, or marked as equal to another term. All reasons are pointed
/// to by a row in a terms table.
///
///
#[derive(Debug)]
pub(crate) enum ProofReason {
    Rule(RuleData),
    // Congrence reasons contain the "old" term id that the new term is equal
    // to. Pairwise equalty proofs are rebuilt at proof reconstruction time.
    CongRow,
    // An identity proof. Used to store a (redundant) proof that a term is equal
    // to itself.
    CongId,
    //
    Fiat { desc: Rc<str> },
}

#[derive(Debug)]
pub(crate) struct RuleData {
    desc: Rc<str>,
    insert_to: Insertable,
    ///  The atoms on the LHS of the rule.
    lhs_atoms: Vec<Vec<QueryEntry>>,
    /// The Atom this is a proof of
    dst_atom: Vec<QueryEntry>,
    /// To fire, a rule must prove that two terms are equal. To do this, we
    /// pick an (arbirary) representative term from the LHS of the rule as
    /// the representative. The fully reconstructed proof will include a
    /// proof that each term on the LHS is equal to its representative.
    representatives: Vec<usize>,
}

impl ProofReason {
    pub(crate) fn arity(&self) -> usize {
        // All start with a proof spec id.
        1 + match self {
            ProofReason::Rule(RuleData { lhs_atoms, .. }) => lhs_atoms.len(),
            ProofReason::CongRow | ProofReason::CongId => 1,
            ProofReason::Fiat { .. } => 0,
        }
    }
}

/// The sort of insertion that an existence proof may correspond to.
#[derive(Debug, Copy, Clone)]
pub(crate) enum Insertable {
    /// An insertion into a function / table.
    Func(FunctionId),
    /// An egglog `union`.
    UnionFind,
}

pub(crate) struct ProofBuilder {
    rule_description: Rc<str>,
    lhs_atoms: Vec<Vec<QueryEntry>>,
    lhs_term_vars: Vec<(Variable, usize /* representative to compare against */)>,
    representatives: IndexSet<Variable>,
}

pub(crate) struct RebuildVars {
    pub(crate) new_term: Variable,
    pub(crate) reason: Variable,
    pub(crate) before_term: Variable,
}

impl ProofBuilder {
    pub(crate) fn new(description: String) -> ProofBuilder {
        ProofBuilder {
            rule_description: description.into(),
            lhs_atoms: Default::default(),
            lhs_term_vars: Default::default(),
            representatives: Default::default(),
        }
    }

    pub(crate) fn add_lhs(&mut self, entries: &[QueryEntry], term_var: Variable) {
        let id_var = entries.last().unwrap().var();
        self.representatives.insert(id_var);
        let to_compare = self.representatives.get_index_of(&id_var).unwrap();
        self.lhs_atoms.push(entries.to_vec());
        self.lhs_term_vars.push((term_var, to_compare));
    }

    /// Generate a proof for a newly rebuilt row.
    pub(crate) fn rebuild_proof(
        &mut self,
        func: FunctionId,
        after: &[QueryEntry],
        vars: RebuildVars,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        // TODO/optimization: we only ever need one CongRow reason.
        let reason_spec = Rc::new(ProofReason::CongRow);
        let reason_table = db.reason_table(&reason_spec);
        let reason_spec_id = db.proof_specs.push(reason_spec);
        let reason_counter = db.reason_counter;
        let func_table = db.funcs[func].table;
        let term_table = db.term_table(func_table);
        let term_counter = db.id_counter;
        let after = after.to_vec();
        move |inner, rb| {
            let old_term = inner.mapping[vars.before_term];
            let reason_id = rb.lookup_or_insert(
                reason_table,
                &[Value::new(reason_spec_id.rep()).into(), old_term],
                &[reason_counter.into()],
                ColumnId::new(2),
            )?;
            let mut entries = Vec::new();
            entries.push(Value::new(func.rep()).into());
            for entry in &after[..after.len() - 1] {
                entries.push(inner.convert(entry));
            }
            // Now get the new term value, inserting it if the term is new.
            let term_result = rb.lookup_or_insert(
                term_table,
                &entries,
                &[term_counter.into(), reason_id.into()],
                ColumnId::from_usize(entries.len()),
            )?;
            inner.mapping.insert(vars.new_term, term_result.into());
            inner.mapping.insert(vars.reason, reason_id.into());
            Ok(())
        }
    }

    fn make_reason(
        &mut self,
        insert_to: Insertable,
        dst_atom: &[QueryEntry],
        reason_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        // NB: we could cache these.
        let spec = Rc::new(ProofReason::Rule(RuleData {
            desc: self.rule_description.clone(),
            insert_to,
            lhs_atoms: self.lhs_atoms.clone(),
            dst_atom: dst_atom.to_vec(),
            representatives: self
                .lhs_term_vars
                .iter()
                .map(|(_, target)| *target)
                .collect(),
        }));
        let spec_table = db.reason_table(&spec);
        let spec_id = db.proof_specs.push(spec);
        let proof_vars: Vec<Variable> = self.lhs_term_vars.iter().map(|(var, _)| *var).collect();
        let reason_counter = db.reason_counter;
        move |inner, rb| {
            let mut args = Vec::with_capacity(proof_vars.len() + 1);
            args.push(Value::new(spec_id.rep()).into());
            for var in &proof_vars {
                args.push(inner.mapping[*var]);
            }
            let x = rb.lookup_or_insert(
                spec_table,
                &args,
                &[reason_counter.into()],
                ColumnId::from_usize(args.len()),
            )?;
            inner.mapping.insert(reason_var, x.into());
            Ok(())
        }
    }

    /// Generate a callback that will add a proof reason to the database and
    /// bind a poitner to that reason to `reason_var`.
    pub(crate) fn union(
        &mut self,
        l: QueryEntry,
        r: QueryEntry,
        reason_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        self.make_reason(Insertable::UnionFind, &[l, r], reason_var, db)
    }

    /// Generate a callback that will add a row to the term database, as well as
    /// a reason for that term existing.
    pub(crate) fn new_row(
        &mut self,
        func: FunctionId,
        entries: Vec<QueryEntry>,
        term_var: Variable,
        reason_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        let make_reason = self.make_reason(Insertable::Func(func), &entries, reason_var, db);
        let func_table = db.funcs[func].table;
        let term_table = db.term_table(func_table);
        let func_val = Value::new(func_table.rep());
        move |inner, rb| {
            make_reason(inner, rb)?;
            let mut translated = Vec::new();
            translated.push(func_val.into());
            for entry in &entries[0..entries.len() - 1] {
                translated.push(inner.convert(entry));
            }
            translated.push(inner.mapping[term_var]);
            // Need to rework the term table building here. It's off. Want to
            // generate it with lookup_or_insert always, requires some
            // knot-tying.
            let todo_remove = 1;
            // translated.push(inner.mapping[reason_var]);
            translated.push(Value::new(10101010).into());
            rb.insert(term_table, &translated)?;
            Ok(())
        }
    }
}

#[derive(Default)]
pub(crate) struct ProofReconstructionState {
    in_progress: HashSet<Value>,
    term_memo: HashMap<Value, Rc<TermProof>>,
    eq_memo: HashMap<(Value, Value), Rc<EqProof>>,
    eq_reason_memo: HashMap<Value, Rc<EqProof>>,

    // maps for "hash-consing" proofs
    id: HashMap<*const TermProof, Rc<EqProof>>,
    backwards: HashMap<*const EqProof, Rc<EqProof>>,
    base: HashMap<*const TermProof, Rc<EqProof>>,
}

impl ProofReconstructionState {
    fn id(&mut self, term: Rc<TermProof>) -> Rc<EqProof> {
        self.id
            .entry(term.as_ref() as *const _)
            .or_insert_with(move || Rc::new(EqProof::Id(term)))
            .clone()
    }

    fn backwards(&mut self, eq: Rc<EqProof>) -> Rc<EqProof> {
        self.backwards
            .entry(eq.as_ref() as *const _)
            .or_insert_with(move || Rc::new(EqProof::Backwards(eq)))
            .clone()
    }

    fn base(&mut self, term: Rc<TermProof>) -> Rc<EqProof> {
        self.base
            .entry(term.as_ref() as *const _)
            .or_insert_with(move || Rc::new(EqProof::Base(term)))
            .clone()
    }
}

// Proof reconstruction code. A lot of this code assumes that it is running
// outside of the "hot path" for an application; it allocates a lot of small
// vectors, does a good amount of not-exactly-stack-safe recursion, etc.

impl EGraph {
    pub(crate) fn explain_term_inner(
        &mut self,
        term_id: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<TermProof> {
        if let Some(prev) = state.term_memo.get(&term_id) {
            return prev.clone();
        }
        assert!(
            state.in_progress.insert(term_id),
            "term id {term_id:?} has a cycle in its explanation!"
        );
        let term_row = self.get_term_row(term_id);
        debug_assert_eq!(term_row[term_row.len() - 2], term_id);
        // We have something like (F x y) => `term_id` + `reason`
        // There are two things to do at this juncture:
        // 1. Explain the children (namely `x` and `y`)
        // 2. Explain anything about `reason`.

        let reason = *term_row.last().unwrap();
        let reason_row = self.get_reason(reason);
        let spec = self.proof_specs[ReasonSpecId::new(reason_row[0].rep())].clone();
        let res = match &*spec {
            ProofReason::Rule(data) => {
                self.create_rule_proof(data, &term_row[1..term_row.len() - 2], &reason_row, state)
            }
            ProofReason::CongRow => self.create_cong_proof(reason_row[1], term_id, state),
            ProofReason::CongId => {
                panic!("CongId is being used as the proof that a term exists (id={term_id:?}); it is really just a proof that two terms are equal")
            }
            ProofReason::Fiat { desc } => {
                let info = &self.funcs[FunctionId::new(term_row[0].rep())];
                let schema = info.schema.clone();
                let func: Rc<str> = info.name.clone().into();
                let desc = desc.clone();
                let row = self.get_term_values(
                    term_row[1..].iter().zip(schema[0..schema.len() - 1].iter()),
                    state,
                );
                Rc::new(TermProof::Fiat { desc, func, row })
            }
        };

        state.in_progress.remove(&term_id);
        state.term_memo.insert(term_id, res.clone());
        res
    }

    pub(crate) fn explain_terms_equal(
        &mut self,
        l: Value,
        r: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<EqProof> {
        if let Some(prev) = state.eq_memo.get(&(l, r)) {
            return prev.clone();
        }
        #[allow(clippy::never_loop)]
        let res = loop {
            // We are using a loop as a block that we can break out of.
            if l == r {
                let term_proof = self.explain_term_inner(l, state);
                break state.id(term_proof);
            }
            let uf_table = self
                .db
                .get_table(self.uf_table)
                .as_any()
                .downcast_ref::<DisplacedTableWithProvenance>()
                .unwrap();

            let Some(steps) = uf_table.get_proof(l, r) else {
                panic!("attempting to explain why two terms ({l:?} and {r:?}) are equal, but they aren't equal");
            };

            assert!(!steps.is_empty(), "empty proof for equality");

            break if steps.len() == 1 {
                let ProofStep { lhs, rhs, reason } = &steps[0];
                assert_eq!(*lhs, l);
                assert_eq!(*rhs, r);
                match reason {
                    UfProofReason::Forward(reason) => {
                        self.create_eq_proof_step(*reason, *lhs, *rhs, state)
                    }
                    UfProofReason::Backward(reason) => {
                        let base = self.create_eq_proof_step(*reason, *lhs, *rhs, state);
                        state.backwards(base)
                    }
                }
            } else {
                let subproofs: Vec<_> = steps
                    .into_iter()
                    .map(|ProofStep { lhs, rhs, reason }| match reason {
                        UfProofReason::Forward(reason) => {
                            self.create_eq_proof_step(reason, lhs, rhs, state)
                        }
                        UfProofReason::Backward(reason) => {
                            let base = self.create_eq_proof_step(reason, lhs, rhs, state);
                            state.backwards(base)
                        }
                    })
                    .collect();
                Rc::new(EqProof::Trans(subproofs))
            };
        };
        state.eq_memo.insert((l, r), res.clone());
        res
    }

    fn create_cong_proof(
        &mut self,
        old_term_id: Value,
        new_term_id: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<TermProof> {
        let old_term = self.get_term_row(old_term_id);
        let old_term_proof = self.explain_term_inner(old_term_id, state);
        let new_term = self.get_term_row(new_term_id);
        let new_term_proof = self.explain_term_inner(new_term_id, state);
        debug_assert_eq!(old_term[0], old_term[1]);
        let info = &self.funcs[FunctionId::new(old_term[0].rep())];
        let func: Rc<str> = info.name.clone().into();
        let schema = info.schema.clone();
        let pairwise_eq = self.lift_to_values(
            old_term[1..]
                .iter()
                .zip(new_term[1..].iter())
                .zip(schema[0..schema.len() - 1].iter()),
            |slf, state, (old, new)| slf.explain_terms_equal(*old, *new, state),
            |(old, new)| {
                assert_eq!(*old, *new, "primitive values must be equal");
                *old
            },
            state,
        );
        Rc::new(TermProof::Cong {
            func,
            old_term: old_term_proof,
            new_term: new_term_proof,
            pairwise_eq,
        })
    }

    fn create_rule_proof(
        &mut self,
        data: &RuleData,
        trunc_term_row: &[Value],
        reason_row: &[Value],
        state: &mut ProofReconstructionState,
    ) -> Rc<TermProof> {
        let RuleData {
            desc,
            insert_to,
            lhs_atoms: _,
            dst_atom,
            representatives,
        } = data;
        let rule_desc = desc.clone();
        let atom_desc: Rc<str> = format!("{dst_atom:?}").into();
        let (func, schema): (Rc<str>, _) = match insert_to {
            Insertable::Func(f) => (
                self.funcs[*f].name.clone().into(),
                self.funcs[*f].schema.clone(),
            ),
            Insertable::UnionFind => ("union".into(), vec![ColumnTy::Id, ColumnTy::Id]),
        };
        let row: Vec<_> = self.get_term_values(trunc_term_row.iter().zip(schema.iter()), state);
        let premises: Vec<_> = reason_row[1..reason_row.len() - 1]
            .iter()
            .map(|prem| self.explain_term_inner(*prem, state))
            .collect();
        let premises_eq: Vec<_> = reason_row[1..reason_row.len() - 1]
            .iter()
            .zip(representatives.iter())
            .map(|(lhs, rhs_ix)| self.explain_terms_equal(*lhs, reason_row[*rhs_ix + 1], state))
            .collect();
        Rc::new(TermProof::FromRule {
            rule_desc,
            atom_desc,
            func,
            row,
            premises,
            premises_eq,
        })
    }

    fn create_eq_proof_step(
        &mut self,
        reason_id: Value,
        l: Value,
        r: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<EqProof> {
        if let Some(prev) = state.eq_reason_memo.get(&reason_id) {
            return prev.clone();
        }
        let reason_row = self.get_reason(reason_id);
        let spec = self.proof_specs[ReasonSpecId::new(reason_row[0].rep())].clone();
        let res = match &*spec {
            ProofReason::Rule(data) => {
                assert!(
                    matches!(data.insert_to, Insertable::UnionFind),
                    "non-UF insertion being used to explain equality"
                );
                let term_proof = self.create_rule_proof(data, &[l, r], &reason_row, state);
                state.base(term_proof)
            }
            ProofReason::CongRow => {
                let proof = self.create_cong_proof(l, r, state);
                state.base(proof)
            }
            ProofReason::CongId => {
                assert_eq!(reason_row[1], l);
                // Maybe this _shouldn't_ happen.
                let term_proof = self.explain_term_inner(reason_row[1], state);
                state.id(term_proof)
            }
            ProofReason::Fiat { .. } => {
                // NB: we could add this if we wanted to.
                panic!("fiat reason being used to explain equality, rather than a row's existence")
            }
        };
        state.eq_reason_memo.insert(reason_id, res.clone());
        res
    }

    fn get_term_values<'a, 'b>(
        &mut self,
        term_with_schema: impl Iterator<Item = (&'a Value, &'b ColumnTy)>,
        state: &mut ProofReconstructionState,
    ) -> Vec<TermValue<TermProof>> {
        self.lift_to_values(
            term_with_schema,
            |slf, state, child| slf.explain_term_inner(*child, state),
            |v| *v,
            state,
        )
    }

    fn lift_to_values<'a, 'b, T, R>(
        &mut self,
        term_with_schema: impl Iterator<Item = (T, &'b ColumnTy)>,
        mut f: impl FnMut(&mut EGraph, &mut ProofReconstructionState, T) -> Rc<R>,
        mut to_value: impl FnMut(T) -> Value,
        state: &mut ProofReconstructionState,
    ) -> Vec<TermValue<R>> {
        term_with_schema
            .map(|(child, ty)| match ty {
                ColumnTy::Id => TermValue::SubTerm(f(self, state, child)),
                ColumnTy::Primitive(p) => TermValue::Prim(format!(
                    "{:?}",
                    PrimitivePrinter {
                        prim: self.db.primitives(),
                        ty: *p,
                        val: to_value(child),
                    }
                )),
            })
            .collect()
    }

    fn get_term_row(&mut self, term_id: Value) -> Vec<Value> {
        let mut atom = Vec::<DstVar>::new();
        let mut cur = 0;
        loop {
            // Iterate over the table by index to avoid borrowing issues with the
            // call to `get_proof`.
            let Some((keys, table)) = self.term_tables.get_index(cur) else {
                panic!("failed to find term with id {term_id:?}")
            };
            {
                let ps = self.db.pool_set();
                let table_ = self.db.get_table(*table);
                let subset = table_.all(ps);
                let rows = table_.scan(subset.as_ref(), ps);
                for (_, row) in rows.iter() {
                    // Problem 1: We aren't finding term 4
                    // Problem 2: There are two term '2's [are we putting them in the wrong order]?
                    let please_remmove = eprintln!("[table {table:?}] row={row:?}");
                }
            }
            let mut rsb = self.db.new_rule_set();
            let mut qb = rsb.new_query();
            for _ in 0..*keys + 1 {
                atom.push(qb.new_var().into());
            }
            atom.push(term_id.into());
            atom.push(qb.new_var().into()); // reason
            qb.add_atom(*table, &atom, iter::empty()).unwrap();
            let mut rb = qb.rules();
            rb.call_external(self.get_first_id, &atom).unwrap();
            rb.build();
            let rs = rsb.build();
            atom.clear();
            self.db.run_rule_set(&rs);
            if let Some(vals) = self.take_side_channel() {
                return vals;
            }
            cur += 1;
        }
    }

    fn get_reason(&mut self, reason_id: Value) -> Vec<Value> {
        let mut atom = Vec::<DstVar>::new();
        let mut cur = 0;
        loop {
            // Iterate over the table by index to avoid borrowing issues with the
            // call to `get_proof`.
            let (arity, table) = self
                .reason_tables
                .get_index(cur)
                .unwrap_or_else(|| panic!("failed to find reason with id {reason_id:?}"));
            let mut rsb = self.db.new_rule_set();
            let mut qb = rsb.new_query();
            for _ in 0..*arity {
                atom.push(qb.new_var().into());
            }
            atom.push(reason_id.into());
            qb.add_atom(*table, &atom, iter::empty()).unwrap();
            let mut rb = qb.rules();
            rb.call_external(self.get_first_id, &atom).unwrap();
            rb.build();
            let rs = rsb.build();
            atom.clear();
            self.db.run_rule_set(&rs);
            if let Some(vals) = self.take_side_channel() {
                return vals;
            }
            cur += 1;
        }
    }
}

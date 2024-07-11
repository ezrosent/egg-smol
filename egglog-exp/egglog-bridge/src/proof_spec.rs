use std::{
    collections::{HashMap, HashSet},
    iter,
    rc::Rc,
};

use core_relations::{
    ColumnId, DisplacedTableWithProvenance, PrimitivePrinter, ProofStep, RuleBuilder, Value,
    WriteVal,
};
use indexmap::{IndexMap, IndexSet};
use numeric_id::{define_id, DenseIdMap, NumericId};
use smallvec::SmallVec;

use crate::{
    proof_dag::{ElementProof, EqProof, Projection, RenderedValue, RowProof},
    rule::{Bindings, DstVar, Variable},
    ColumnTy, EGraph, FunctionId, QueryEntry, Result,
};

define_id!(pub(crate) ProofSpecId, u32, "A unique identifier for the step in a proof.");

/// A specification for what is encoded in the (first step of) the proof of a
/// particular term in the database.
///
/// Proofs are stored in dynamically-generated "trace tables" (one per arity).
/// The first entry in any proof row is a [`ProofSpecId`] that points to the
/// given [`ProofSpec`] that can be used to reconstruct the step in the proof,
/// along with any dependencies: they explain the contents of the row of a trace
/// table.
#[derive(Debug)]
pub(crate) enum ProofSpec {
    /// The proof of a row `T(a0, ... , an)`. This involves:
    ///  * The term `T(a0, ... , an)` itself.
    ///  * The rule that introduced the term.
    ///  * The proofs of each of the a0, ... , an used when creating the term. Note
    ///    that each ai may have more than one relevant proof:
    ///    E.g. For the rule `Path(x, z) :- Path(x, y), Path(y, z)`, we care about the
    ///    "left" and "right" proofs for `y` (namely, the proofs of `Path(x, y)` and
    ///    `Path(y, z)` respectively).
    RowExists {
        desc: String,
        insert_to: Insertable, // Table name
        atom: Vec<QueryEntry>,
        n_proofs: usize,
        proofs_for: DenseIdMap<usize /* arg */, Vec<ArgIndex<usize>>>,
    },

    /// A proof that a row `T(a0, ... , an)` is equal to a row `T(b0, ... , bn)`
    /// because we have for each `ai = bi`.
    ///
    /// Note that these are just 'administrative' proofs. Interesting "semantic"
    /// proofs that, say Add(1, 2) = 3 will show up as `RowExists` proofs
    /// inserting into the special "Displaced" storing an equivalence relation.
    ///
    /// EqProofs are laid out with both terms (the `ai`s and `bi`s) followed by
    /// the proof of the original row `T(a0,...,an)`. The proofs that each `ai =
    /// bi` are reconstructed "out of band" from the proof-procducing union-find
    /// table.
    ///
    /// NB: we ought to be able to cut down on the size of some rebuild proofs
    /// by only storing the rows that changed, but we would need to do be able
    /// to run a little more business logic in core_relations before that
    /// becomes easy.
    RowEq { func: FunctionId, arity: usize },

    /// A proof that `x = y` because we have some `T(a0, ... , an, x)` and
    /// `T(a0, ... , an, y)`.
    ///
    /// Proofs of congruence contain the `ai`, the `x` and the `y` and the
    /// proofs of the two rows.
    Cong { func: FunctionId, arity: usize },

    /// External tuples loaded directly as base values in the database.
    Fiat {
        func: FunctionId,
        arity: usize,
        desc: String,
    },
}

/// The sort of insertion that an existence proof may correspond to.
#[derive(Debug, Copy, Clone)]
pub(crate) enum Insertable {
    /// An insertion into a function / table.
    Func(FunctionId),
    /// An egglog `union`.
    UnionFind,
}

#[derive(Clone)]
pub(crate) enum InsertKind {
    Lookup { ts_var: QueryEntry },
    Insert,
}

impl ProofSpec {
    pub(crate) fn arity(&self) -> usize {
        // Add one for storing the ProofSpecId
        1 + match self {
            ProofSpec::RowExists { atom, n_proofs, .. } => atom.len() + n_proofs,
            // Equality proofs
            // *2 because we store the old and the new row.
            // +1 for the proof of the original row.
            ProofSpec::RowEq { arity, .. } => *arity * 2 + 1,
            // +1 for the extra value.
            // +2 for the two proofs.
            ProofSpec::Cong { arity, .. } => *arity + 1 + 2,
            ProofSpec::Fiat { arity, .. } => *arity,
        }
    }
}

pub(crate) fn cong_row(
    proof_spec: ProofSpecId,
    n_args: usize,
    cur: &[Value],
    new: &[Value],
) -> SmallVec<[Value; 8]> {
    let mut res = SmallVec::new();
    res.push(Value::new(proof_spec.rep()));
    // Original key.
    res.extend_from_slice(&cur[0..n_args]);
    // The old and the new value.
    res.push(cur[n_args]);
    res.push(new[n_args]);
    // The proofs for the old and the new row.
    res.push(*cur.last().unwrap());
    res.push(*new.last().unwrap());
    res
}

pub(crate) struct ProofBuilder {
    rule_description: String,
    // TODO: these can just be format!("v{variable:?}") for now, but we should
    // support callers passing names to variables.
    variables: IndexMap<Variable, ProofVarInfo>,
    counter: usize,
}

impl ProofBuilder {
    pub(crate) fn new(description: String) -> ProofBuilder {
        ProofBuilder {
            rule_description: description,
            variables: Default::default(),
            counter: 0,
        }
    }

    pub(crate) fn add_lhs(&mut self, entries: &[QueryEntry], proof_var: Variable) {
        for (i, entry) in entries.iter().enumerate() {
            match entry {
                QueryEntry::Var { id: var, name } => {
                    let info = self.variables.entry(*var).or_insert_with(|| ProofVarInfo {
                        name: name
                            .as_ref()
                            .map(|x| String::from(x.clone()))
                            .unwrap_or_else(|| format!("v{var:?}")),
                        args: Default::default(),
                    });
                    info.args.push(ArgIndex {
                        proof: proof_var,
                        index: i,
                    });
                }
                QueryEntry::Const(_) => continue,
            }
        }
    }

    /// Generate a proof for a newly rebuilt row.
    pub(crate) fn rebuild_proof(
        &mut self,
        func: FunctionId,
        before: &[QueryEntry],
        after: &[QueryEntry],
        proof_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        assert_eq!(
            before.len(),
            after.len(),
            "before and after rows should have the same length"
        );
        let before_proof = self.variables[&before[0].var()].args[0].proof;
        // NB: we will probably have duplicate proof specs here, and we could
        // save a little space if we reused them between calls to rebuild.
        let proof_spec = ProofSpec::RowEq {
            func,
            arity: before.len(),
        };
        let proof_arity = proof_spec.arity();
        let trace_table = db.trace_table(proof_arity);
        let spec_id = db.proof_specs.push(proof_spec.into());
        let proof_ctr = db.trace_counter;

        let before = SmallVec::<[_; 4]>::from_iter(before.iter().cloned());
        let after = SmallVec::<[_; 4]>::from_iter(after.iter().cloned());
        move |bindings, rb| {
            let before = bindings.convert_all(&before);
            let after = bindings.convert_all(&after);
            let mut row = Vec::with_capacity(proof_arity);
            row.push(DstVar::Const(Value::new(spec_id.rep())));
            row.extend_from_slice(&before);
            row.extend_from_slice(&after);
            row.push(bindings.convert(&before_proof.into()));
            let proof_dst_var = rb.lookup_or_insert(
                trace_table,
                &row,
                &[proof_ctr.into()],
                ColumnId::from_usize(proof_arity),
            )?;
            bindings
                .mapping
                .insert(proof_var, DstVar::Var(proof_dst_var));
            Ok(())
        }
    }

    fn arity(&self, insert_to: Insertable, db: &EGraph) -> usize {
        match insert_to {
            Insertable::Func(f) => db.funcs[f].schema.len(),
            Insertable::UnionFind => 2,
        }
    }

    /// Generate a callback that will add a proof row to the database
    /// corresponding to the given row being added.
    pub(crate) fn set(
        &mut self,
        insert_to: Insertable,
        entries: Vec<QueryEntry>,
        proof_var: Variable,
        insert_kind: InsertKind,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> {
        let mut var_to_index = HashMap::new();
        let mut variables = Vec::new();
        assert_eq!(entries.len(), self.arity(insert_to, db));
        for (i, entry) in entries.iter().enumerate() {
            match entry {
                QueryEntry::Var { id: v, .. } => {
                    var_to_index.entry(*v).or_insert(i);
                    variables.push(
                        self.variables
                            .get(v)
                            .map(|info| info.name.clone())
                            .unwrap_or_else(|| format!("v{v:?}")),
                    )
                }
                QueryEntry::Const(c) => {
                    variables.push(format!("{c:?}"));
                }
            }
        }
        let mut proof_vars = IndexSet::new();
        let mut proofs_for: DenseIdMap<usize, Vec<ArgIndex<usize>>> = Default::default();
        let mut proofs_for_iter = Vec::new();
        for var in entries.iter().filter_map(|entry| match entry {
            QueryEntry::Var { id, .. } => Some(id),
            QueryEntry::Const(_) => None,
        }) {
            let mut proof_args = Vec::new();
            if let Some(info) = self.variables.get(var) {
                proof_args.extend(info.args.iter().map(|ArgIndex { proof, index }| {
                    proof_vars.insert(*proof);
                    let proof_index = proof_vars.get_index_of(proof).unwrap();
                    ArgIndex {
                        proof: proof_index,
                        index: *index,
                    }
                }));
            }
            proofs_for_iter.push((*var, proof_args));
        }
        for (var, proofs) in proofs_for_iter {
            proofs_for.insert(var_to_index[&var], proofs);
        }

        let new_spec = ProofSpec::RowExists {
            desc: format!("{} atom {}", self.rule_description, self.counter),
            insert_to,
            atom: entries.clone(),
            n_proofs: proof_vars.len(),
            proofs_for,
        };
        self.counter += 1;
        let arity = new_spec.arity();
        let trace_table = db.trace_table(arity);
        let spec_id = db.proof_specs.push(new_spec.into());
        let ctr = db.trace_counter;
        // Add the proof we are adding to the environment for further atoms
        // here. They may show up as dependencies themselves.
        if let InsertKind::Lookup { .. } = insert_kind {
            // We are introducing the final column in this atom. Future atoms
            // should pick up the proof.
            let var = entries.last().unwrap().var();
            self.variables
                .entry(var)
                .or_insert_with(|| ProofVarInfo {
                    name: format!("v{var:?}"),
                    args: Default::default(),
                })
                .args
                .push(ArgIndex {
                    proof: proof_var,
                    index: entries.len() - 1,
                });
        }
        move |bindings, rb| {
            let mut row = Vec::with_capacity(1 + entries.len() + proof_vars.len());
            row.push(DstVar::Const(Value::new(spec_id.rep())));
            // Now insert the row:
            for entry in &entries {
                row.push(bindings.convert(entry));
            }
            // And now insert all relevant proofs:
            for proof in &proof_vars {
                row.push(bindings.convert(&QueryEntry::Var {
                    id: *proof,
                    name: None,
                }));
            }
            match &insert_kind {
                InsertKind::Lookup { ts_var } => {
                    let v = bindings.mapping[proof_var];
                    // Someone already has a proof variable for us to use, just do a
                    // raw `set`. If the relevant row wasn't inserted at the
                    // current timestamp then avoid inserting.
                    row.push(v);
                    rb.insert_if_eq(
                        trace_table,
                        bindings.convert(ts_var),
                        bindings.next_ts.to_value().into(),
                        &row,
                    )?;
                }
                InsertKind::Insert => {
                    // We need to bind the proof variable. Just lookup-or-insert one
                    // using the proof counter.
                    let var = rb.lookup_or_insert(
                        trace_table,
                        &row,
                        &[WriteVal::Counter(ctr)],
                        ColumnId::from_usize(row.len()),
                    )?;
                    bindings.mapping.insert(proof_var, DstVar::Var(var));
                }
            }

            Ok(())
        }
    }
}

struct ProofVarInfo {
    name: String,
    args: Vec<ArgIndex<Variable>>,
}

#[derive(Debug)]
pub(crate) struct ArgIndex<T> {
    /// An identifier for a proof (e.g. the index of the proof in the proof
    /// spec, or the variable bound to the proof in a query).
    proof: T,
    /// The index within the term prooved by the indicated proof.
    index: usize,
}

impl ProofSpec {
    fn expand_eq_proof(
        &self,
        proof_term: &[Value],
        egraph: &mut EGraph,
        memo: &mut Memo,
    ) -> Rc<EqProof> {
        // We're assuming that proof_term doesn't include the ProofSpecId.
        match self {
            ProofSpec::RowExists { .. } => {
                // "exists" rows can be eq proofs if they are proofs for
                // insertion into the union-find.
                Rc::new(EqProof::Base(self.expand_row_proof(proof_term, egraph, memo)))
            }
            ProofSpec::Cong { func, arity } => {
                let arity = *arity;
                let mut row: Vec<RenderedValue> =
                    egraph.render_row(*func, &proof_term[0..arity]).collect();
                let x = row.pop().unwrap();
                let y = egraph.render_value(
                    proof_term[arity],
                    *egraph.funcs[*func].schema.last().unwrap(),
                );
                let x_proof = get_row_proof(proof_term[arity + 1], egraph, memo);
                let y_proof = get_row_proof(proof_term[arity + 2], egraph, memo);
                let func_name = egraph.funcs[*func].name.clone();
                Rc::new(EqProof::Cong {
                    func: func_name,
                    x,
                    y,
                    key: row,
                    x_proof,
                    y_proof,
                })
            }
            ProofSpec::RowEq {..} => panic!("attempt to expand a proof that two rows are equal as a proof that two values are equal"),
            ProofSpec::Fiat {..} => panic!("attempt to expand a base proof of a row as a proof that two values are equal"),
        }
    }
    fn expand_row_proof(
        &self,
        proof_term: &[Value],
        egraph: &mut EGraph,
        memo: &mut Memo,
    ) -> Rc<RowProof> {
        // We're assuming that proof_term doesn't include the ProofSpecId.
        match self {
            ProofSpec::RowExists {
                desc,
                insert_to,
                atom,
                proofs_for,
                ..
            } => {
                let arity = atom.len();
                let (row, name) = match insert_to {
                    Insertable::Func(func) => {
                        let row = Vec::from_iter(egraph.render_row(*func, &proof_term[0..arity]));
                        (row, egraph.funcs[*func].name.clone())
                    }
                    Insertable::UnionFind => (
                        vec![
                            egraph.render_value(proof_term[0], ColumnTy::Id),
                            egraph.render_value(proof_term[1], ColumnTy::Id),
                        ],
                        "union".to_string(),
                    ),
                };
                let mut element_proofs = Vec::new();
                for (i, val) in row.into_iter().enumerate() {
                    let mut projections = Vec::new();
                    if let Some(proofs) = proofs_for.get(i) {
                        for ArgIndex { proof, index } in proofs {
                            projections.push(Projection {
                                field: *index,
                                proof: get_row_proof(proof_term[arity + *proof], egraph, memo),
                            });
                        }
                    }
                    element_proofs.push(ElementProof {
                        val,
                        proofs: projections,
                    })
                }
                Rc::new(RowProof::Exists {
                    rule_desc: desc.clone(),
                    atom_desc: format!(
                        "{}",
                        DisplayList(atom.iter().map(|x| x.render()).collect(), ", ")
                    ),
                    func: name,
                    row: element_proofs,
                })
            }
            ProofSpec::RowEq { func, arity } => {
                let old_row_proof = get_row_proof(*proof_term.last().unwrap(), egraph, memo);
                let new_row =
                    Vec::from_iter(egraph.render_row(*func, &proof_term[*arity..(*arity * 2)]));
                let mut eq_proofs = Vec::new();
                for (old, new) in proof_term[0..*arity]
                    .iter()
                    .zip(proof_term[*arity..(*arity * 2)].iter())
                {
                    if old == new {
                        eq_proofs.push(memo.id_proof.clone());
                        continue;
                    }

                    let uf_table = egraph
                        .db
                        .get_table(egraph.uf_table)
                        .as_any()
                        .downcast_ref::<DisplacedTableWithProvenance>()
                        .unwrap();
                    let steps = uf_table.get_proof(*old, *new).unwrap_or_else(|| {
                        panic!(
                            "values {old:?} and {new:?} are not equivalent even though they form part of a proof that two rows are equivalent"
                        )
                    });
                    let mut convert_step = |step: ProofStep| match step {
                        ProofStep::Forward(p) => get_eq_proof(p, egraph, memo),
                        ProofStep::Backward(p) => {
                            Rc::new(EqProof::Backwards(get_eq_proof(p, egraph, memo)))
                        }
                    };
                    if steps.is_empty() {
                        eq_proofs.push(memo.id_proof.clone());
                    } else if steps.len() == 1 {
                        eq_proofs.push(convert_step(steps.into_iter().next().unwrap()))
                    } else {
                        eq_proofs.push(Rc::new(EqProof::Trans(
                            steps.into_iter().map(convert_step).collect(),
                        )))
                    }
                }
                Rc::new(RowProof::RowEq {
                    func: egraph.funcs[*func].name.clone(),
                    old_row: old_row_proof,
                    new_row,
                    eq_proofs,
                })
            }
            ProofSpec::Fiat { func, desc, .. } => Rc::new(RowProof::Fiat {
                desc: desc.clone(),
                func: egraph.funcs[*func].name.clone(),
                row: egraph.render_row(*func, proof_term).collect::<Vec<_>>(),
            }),
            ProofSpec::Cong { .. } => {
                panic!("attempt to use congruence as an existence proof for a row")
            }
        }
    }
}

pub(crate) fn get_row_proof(proof_id: Value, egraph: &mut EGraph, memo: &mut Memo) -> Rc<RowProof> {
    if let Some(proof) = memo.row_proofs.get(&proof_id) {
        return proof.clone();
    }
    if !memo.searching.insert(proof_id) {
        panic!("detected cycle: saw {proof_id:?} twice; this is a bug!");
    }
    let vals = get_proof_inner(proof_id, egraph);
    let spec_id = ProofSpecId::new(vals[0].rep());
    let spec = egraph.proof_specs[spec_id].clone();
    let res = spec.expand_row_proof(&vals[1..vals.len() - 1], egraph, memo);
    memo.row_proofs.insert(proof_id, res.clone());
    memo.searching.remove(&proof_id);
    res
}

fn get_eq_proof(proof_id: Value, egraph: &mut EGraph, memo: &mut Memo) -> Rc<EqProof> {
    if let Some(proof) = memo.eq_proofs.get(&proof_id) {
        return proof.clone();
    }
    let vals = get_proof_inner(proof_id, egraph);
    let spec_id = ProofSpecId::new(vals[0].rep());
    let spec = egraph.proof_specs[spec_id].clone();
    let res = spec.expand_eq_proof(&vals[1..vals.len() - 1], egraph, memo);
    memo.eq_proofs.insert(proof_id, res.clone());
    res
}

fn get_proof_inner(proof_id: Value, egraph: &mut EGraph) -> Vec<Value> {
    let mut atom = Vec::<DstVar>::new();
    let mut cur = 0;
    loop {
        // Iterate over the table by index to avoid borrowing issues with the
        // call to `get_proof`.
        let (arity, table) = egraph
            .trace_tables
            .get_index(cur)
            .unwrap_or_else(|| panic!("failed to find proof with id {proof_id:?}"));
        let mut rsb = egraph.db.new_rule_set();
        let mut qb = rsb.new_query();
        for _ in 0..*arity {
            atom.push(qb.new_var().into());
        }
        atom.push(proof_id.into());
        qb.add_atom(*table, &atom, iter::empty()).unwrap();
        let mut rb = qb.rules();
        rb.call_external(egraph.get_first_id, &atom).unwrap();
        rb.build();
        let rs = rsb.build();
        atom.clear();
        egraph.db.run_rule_set(&rs);
        if let Some(vals) = egraph.take_side_channel() {
            return vals;
        }
        cur += 1;
    }
}

pub(crate) struct Memo {
    row_proofs: HashMap<Value, Rc<RowProof>>,
    eq_proofs: HashMap<Value, Rc<EqProof>>,
    /// Note that there should _always_ be an acyclic proof for a row in the
    /// database. We keep this set around to catch cycles before they turn into
    /// infinite loops / stack overflows, but cycles always indicate a bug.
    searching: HashSet<Value>,
    id_proof: Rc<EqProof>,
}

impl Default for Memo {
    fn default() -> Memo {
        Memo {
            row_proofs: Default::default(),
            eq_proofs: Default::default(),
            searching: Default::default(),
            id_proof: Rc::new(EqProof::Trans(Vec::new())),
        }
    }
}

impl EGraph {
    /// Convert a row into a series of [`RenderedValue`]s for use in proofs.
    ///
    /// # Panics
    /// This method will panic if the row does not match `func`'s arity.
    fn render_row<'a>(
        &'a self,
        func: FunctionId,
        row: &'a [Value],
    ) -> impl Iterator<Item = RenderedValue> + 'a {
        let info = &self.funcs[func];
        assert_eq!(
            row.len(),
            info.schema.len(),
            "arity mismatch for function {func:?} aka {}",
            info.name,
        );
        row.iter()
            .zip(info.schema.iter())
            .map(|(val, ty)| self.render_value(*val, *ty))
    }

    /// Convert a value into a [`RenderedValue`] for use in proofs.
    fn render_value(&self, val: Value, ty: ColumnTy) -> RenderedValue {
        match ty {
            ColumnTy::Id => RenderedValue::Id(val.index()),
            ColumnTy::Primitive(prim) => RenderedValue::Prim(format!(
                "{:?}",
                PrimitivePrinter {
                    prim: self.db.primitives(),
                    ty: prim,
                    val,
                }
            )),
        }
    }
}

/// A basic helper for display-formatting lists of items.
pub(crate) struct DisplayList<T>(pub Vec<T>, pub &'static str);

impl<T: std::fmt::Display> std::fmt::Display for DisplayList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();
        if let Some(first) = iter.next() {
            write!(f, "{first}")?;
            for item in iter {
                write!(f, "{}{item}", self.1)?;
            }
        }
        Ok(())
    }
}

use smallvec::SmallVec;
use thiserror::Error;

use crate::{
    actions::RuleBuilder,
    common::{DenseIdMap, HashMap, NumericId},
    define_id,
    function::Value,
    schema::{ColumnTy, FunctionId},
    Db, Result,
};

use self::plan::{plan_query, Plan, PlanStrategy};

pub(crate) mod execute;
pub(crate) mod offset_frame;
pub(crate) mod plan;
#[cfg(test)]
mod tests;

define_id!(pub Variable, u32, "a variable in a query");
define_id!(pub(crate) AtomId, u32,
    "an identifier for an atom (i.e. a function symbol and a list of variables/constants) in a query");
define_id!(pub(crate) AtomIdx, u32, "an index into an atom's list of variables");

pub(crate) struct VarInfo {
    ty: ColumnTy,
    occurrences: Vec<SubAtom>,
}

impl VarInfo {
    pub(crate) fn ty(&self) -> &ColumnTy {
        &self.ty
    }
}

pub(crate) struct Atom {
    func: FunctionId,
    var_to_atom: HashMap<Variable, AtomIdx>,
    atom_to_var: DenseIdMap<AtomIdx, Variable>,
    equal: Vec<(AtomIdx, AtomIdx)>,
    constants: Vec<(AtomIdx, Value)>,
}

impl Atom {
    pub(crate) fn func(&self) -> FunctionId {
        self.func
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SubAtom {
    pub(crate) atom: AtomId,
    pub(crate) vars: SmallVec<[AtomIdx; 4]>,
}

impl SubAtom {
    fn new(atom: AtomId) -> SubAtom {
        SubAtom {
            atom,
            vars: Default::default(),
        }
    }
}

pub(crate) struct Query {
    pub(crate) var_info: DenseIdMap<Variable, VarInfo>,
    pub(crate) atoms: DenseIdMap<AtomId, Atom>,
}

impl Query {
    pub(crate) fn plan(
        &self,
        strategy: PlanStrategy,
        sizes: impl IntoIterator<Item = (AtomId, usize)>,
    ) -> Plan {
        plan_query(self, strategy, sizes)
    }
}

pub struct QueryBuilder<'a, 'pool, 'outer> {
    n_vars: usize,
    n_atoms: usize,
    var_info: DenseIdMap<Variable, VarInfo>,
    atoms: DenseIdMap<AtomId, Atom>,
    db: &'a mut Db<'pool, 'outer>,
}

#[derive(Copy, Clone, Debug)]
pub enum QueryEntry {
    Var(Variable),
    Const(Value),
}

impl From<Variable> for QueryEntry {
    fn from(var: Variable) -> Self {
        QueryEntry::Var(var)
    }
}

impl From<Value> for QueryEntry {
    fn from(val: Value) -> Self {
        QueryEntry::Const(val)
    }
}

#[derive(Error, Debug)]
pub(crate) enum QueryError {
    #[error(
        "variable {var:?} declared as {declared:?} but used as {used_as:?} in function {func:?}"
    )]
    TypeError {
        var: Variable,
        declared: ColumnTy,
        used_as: ColumnTy,
        func: FunctionId,
    },

    #[error("atom {atom:?} binds {func:?} with {got} arguments, expected {expected}")]
    ArityMismatch {
        atom: AtomId,
        func: FunctionId,
        expected: usize,
        got: usize,
    },
}

impl<'a, 'pool, 'outer> QueryBuilder<'a, 'pool, 'outer> {
    pub(crate) fn new(db: &'a mut Db<'pool, 'outer>) -> QueryBuilder<'a, 'pool, 'outer> {
        QueryBuilder {
            n_vars: 0,
            n_atoms: 0,
            var_info: DenseIdMap::new(),
            atoms: DenseIdMap::new(),
            db,
        }
    }
    pub fn new_var(&mut self, name: &str, ty: ColumnTy) -> Variable {
        assert!(
            self.n_vars < u32::MAX as usize,
            "too many variables in a query"
        );
        let var = Variable::with_context(self.n_vars as u32, name);
        self.n_vars += 1;
        self.var_info.insert(
            var,
            VarInfo {
                ty,
                occurrences: Vec::new(),
            },
        );
        var
    }

    pub fn add_atom(&mut self, func: FunctionId, args: &[QueryEntry]) {
        self.add_atom_with_id(func, args);
    }

    pub(crate) fn add_atom_with_id(&mut self, func: FunctionId, args: &[QueryEntry]) -> AtomId {
        let atom = AtomId::from_usize(self.n_atoms);
        let mut within_atom = HashMap::default();
        let mut equal = Vec::new();
        let mut constants = Vec::new();
        for (i, arg) in args.iter().copied().enumerate() {
            let atom_ix = AtomIdx::from_usize(i);
            match arg {
                QueryEntry::Var(var) => {
                    within_atom
                        .entry(var)
                        .or_insert_with(Vec::new)
                        .push(atom_ix);
                }
                QueryEntry::Const(c) => constants.push((atom_ix, c)),
            }
        }
        for (_, idxs) in &within_atom {
            if idxs.len() == 1 {
                continue;
            }
            let fst = idxs[0];
            for snd in &idxs[1..] {
                equal.push((fst, *snd));
            }
        }
        self.n_atoms += 1;
        let mut atom_to_var = DenseIdMap::new();
        let mut var_to_atom = HashMap::default();
        for (i, arg) in args.iter().enumerate() {
            match arg {
                QueryEntry::Var(var) => {
                    let atom = AtomIdx::from_usize(i);
                    atom_to_var.insert(atom, *var);
                    var_to_atom.insert(*var, atom);
                }
                QueryEntry::Const(_) => {}
            }
        }
        self.atoms.insert(
            atom,
            Atom {
                func,
                atom_to_var,
                var_to_atom,
                equal,
                constants,
            },
        );
        let mut vars = HashMap::default();
        for (i, arg) in args.iter().copied().enumerate() {
            match arg {
                QueryEntry::Var(var) => {
                    vars.entry(var)
                        .or_insert_with(SmallVec::new)
                        .push(AtomIdx::from_usize(i));
                }
                QueryEntry::Const(_) => {}
            }
        }
        for (var, indices) in vars {
            self.var_info
                .get_mut(var)
                .unwrap()
                .occurrences
                .push(SubAtom {
                    atom,
                    vars: indices,
                });
        }
        atom
    }

    fn validate(&self) -> Result<()> {
        for (var, info) in self.var_info.iter() {
            let declared_ty = info.ty;
            for occ in &info.occurrences {
                let atom = self.atoms.get(occ.atom).expect("atom must be known");
                let func = atom.func();
                let schema = self.db.funcs()[func].schema();
                for ix in occ.vars.iter().copied() {
                    let use_ty = if ix.index() == schema.args().len() {
                        *schema.ret()
                    } else {
                        schema.args()[ix.index()]
                    };
                    if declared_ty != use_ty {
                        return Err(QueryError::TypeError {
                            var,
                            declared: declared_ty,
                            used_as: use_ty,
                            func,
                        }
                        .into());
                    }
                }
            }
        }
        for (atom_id, atom) in self.atoms.iter() {
            let arity = self.db.funcs()[atom.func].schema().arity();
            let binding_arity = atom.atom_to_var.iter().count();
            if binding_arity + atom.constants.len() != arity + 1 {
                return Err(QueryError::ArityMismatch {
                    atom: atom_id,
                    func: atom.func,
                    expected: arity + 1,
                    got: binding_arity,
                }
                .into());
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn build(self) -> Result<Query> {
        Ok(self.finish()?.0)
    }

    fn finish(self) -> Result<(Query, &'a mut Db<'pool, 'outer>)> {
        self.validate()?;
        Ok((
            Query {
                var_info: self.var_info,
                atoms: self.atoms,
            },
            self.db,
        ))
    }

    pub fn rule(self) -> Result<RuleBuilder<'a, 'pool, 'outer>> {
        let (query, db) = self.finish()?;
        Ok(RuleBuilder::new(Some(query), db))
    }
}

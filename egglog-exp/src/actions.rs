//! Instructions to run on the result of a query.

use thiserror::Error;

use crate::{
    common::{DenseIdMap, NumericId},
    define_id,
    free_join::{Query, QueryEntry, Variable},
    function::{table::Timestamp, Value},
    pool::PoolRef,
    primitives::PrimitiveFunctionId,
    schema::{ColumnTy, FunctionId, Schema},
    Db, Result,
};

define_id!(pub RuleId, u32, "a rule in a particular database");

pub(crate) struct Rule {
    pub(crate) query: Option<Query>,
    instrs: Vec<Instr>,
    pub(crate) next_run: Timestamp,
}

impl Rule {
    pub(crate) fn instrs(&self) -> &[Instr] {
        &self.instrs
    }
}

struct RuleVarInfo {
    ty: ColumnTy,
}

#[derive(Debug, Error)]
pub enum RuleError {
    #[error("arity mismatch in function {func:?}: expected {expected} arguments, got {actual}")]
    ArityMismatch {
        func: FunctionId,
        expected: usize,
        actual: usize,
    },

    #[error("arity mismatch in primitive {func:?}: expected {expected} arguments, got {actual}")]
    PrimitiveArityMismatch {
        func: PrimitiveFunctionId,
        expected: usize,
        actual: usize,
    },

    #[error("type mismatch in function {func:?}: expected {expected:?}, got {actual:?}")]
    FunctionTypeError {
        func: FunctionId,
        expected: ColumnTy,
        actual: ColumnTy,
    },

    #[error("attempt to assign variable of type {var_ty:?} to function {func:?} with return type {func_ty:?}")]
    FunctionReturnValueMisMatch {
        func: FunctionId,
        var_ty: ColumnTy,
        func_ty: ColumnTy,
    },

    #[error("type mismatch in primitive function {func:?}: expected {expected:?}, got {actual:?}")]
    PrimitiveTypeError {
        func: PrimitiveFunctionId,
        expected: ColumnTy,
        actual: ColumnTy,
    },

    #[error("attempt to compare variables of two different types {left:?} and {right:?}")]
    InvalidComparison { left: ColumnTy, right: ColumnTy },

    #[error("attempt to union variable of non-id type")]
    InvalidUnion { var: Variable, ty: ColumnTy },
}

pub struct RuleBuilder<'a, 'pool, 'outer> {
    /// An optional query that is used to bind the starting variables for the rule.
    ///
    /// Rules without a query are run "standalone" with no starting bindings.
    query: Option<Query>,
    /// Information about variables bound by the actions, as opposed to by the query.
    vars: DenseIdMap<Variable, RuleVarInfo>,
    insts: Vec<Instr>,
    db: &'a mut Db<'pool, 'outer>,
}

impl<'a, 'pool, 'outer> RuleBuilder<'a, 'pool, 'outer> {
    pub(crate) fn new(query: Option<Query>, db: &'a mut Db<'pool, 'outer>) -> Self {
        let n_ids = if let Some(q) = &query {
            q.var_info.n_ids()
        } else {
            0
        };
        let mut vars = DenseIdMap::with_capacity(n_ids);
        vars.reserve_space(Variable::from_usize(n_ids));
        RuleBuilder {
            query,
            vars,
            insts: Vec::new(),
            db,
        }
    }
    pub fn finish(self) -> RuleId {
        self.db.add_rule(Rule {
            query: self.query,
            instrs: self.insts,
            next_run: Timestamp::new(0),
        })
    }
    pub fn lookup_with_default(
        &mut self,
        func: FunctionId,
        args: &[QueryEntry],
    ) -> Result<Variable> {
        self.validate_func(func, args)?;
        let ret_ty = *self.db.funcs()[func].schema().ret();
        let res = self.vars.push(RuleVarInfo { ty: ret_ty });
        self.insts.push(Instr::LookupWithDefault {
            func,
            args: args.to_vec(),
            dst: res,
        });
        Ok(res)
    }

    pub fn lookup(&mut self, func: FunctionId, args: &[QueryEntry]) -> Result<Variable> {
        self.validate_func(func, args)?;
        let ret_ty = *self.db.funcs()[func].schema().ret();
        let res = self.vars.push(RuleVarInfo { ty: ret_ty });
        self.insts.push(Instr::Lookup {
            func,
            args: args.to_vec(),
            dst: res,
        });
        Ok(res)
    }

    pub fn union(&mut self, a: Variable, b: Variable) -> Result<()> {
        let a_ty = self.get_ty(a);
        let b_ty = self.get_ty(b);
        if a_ty != ColumnTy::Id {
            return Err(RuleError::InvalidUnion { var: a, ty: a_ty }.into());
        }
        if b_ty != ColumnTy::Id {
            return Err(RuleError::InvalidUnion { var: b, ty: b_ty }.into());
        }

        self.insts.push(Instr::Union(a, b));
        Ok(())
    }

    pub fn insert(&mut self, func: FunctionId, args: &[QueryEntry], ret: QueryEntry) -> Result<()> {
        self.validate_func(func, args)?;
        let ret_ty = *self.db.funcs()[func].schema().ret();
        match ret {
            QueryEntry::Var(var) => {
                let var_ty = self.get_ty(var);
                if ret_ty != var_ty {
                    return Err(RuleError::FunctionReturnValueMisMatch {
                        func,
                        var_ty,
                        func_ty: ret_ty,
                    }
                    .into());
                }
            }
            QueryEntry::Const(_) => {
                // See the comment in validate_args
            }
        }

        self.insts.push(Instr::Insert {
            func,
            args: args.to_vec(),
            ret,
        });
        Ok(())
    }

    pub fn prim(&mut self, func: PrimitiveFunctionId, args: &[QueryEntry]) -> Result<Variable> {
        self.validate_prim(func, args)?;
        let schema = self.db.prims_mut().get_schema(func);
        let res = self.vars.push(RuleVarInfo { ty: *schema.ret() });
        self.insts.push(Instr::Prim {
            func,
            args: args.to_vec(),
            dst: res,
        });
        Ok(res)
    }

    pub fn assert_eq(&mut self, a: QueryEntry, b: QueryEntry) -> Result<()> {
        self.validate_comparison(a, b)?;
        self.insts.push(Instr::AssertEq(a, b));
        Ok(())
    }

    pub fn assert_ne(&mut self, a: QueryEntry, b: QueryEntry) -> Result<()> {
        self.validate_comparison(a, b)?;
        self.insts.push(Instr::AssertNe(a, b));
        Ok(())
    }

    pub fn remove(&mut self, func: FunctionId, args: &[QueryEntry]) -> Result<()> {
        self.validate_func(func, args)?;
        self.insts.push(Instr::Remove {
            func,
            args: args.to_vec(),
        });
        Ok(())
    }

    pub fn tie_break(&mut self, a: Variable, b: Variable) -> Result<(Variable, Variable)> {
        self.validate_comparison(a.into(), b.into())?;
        let a_ty = self.get_ty(a);
        let min = self.vars.push(RuleVarInfo { ty: a_ty });
        let max = self.vars.push(RuleVarInfo { ty: a_ty });
        self.insts.push(Instr::TieBreak { a, b, min, max });
        Ok((min, max))
    }

    fn get_ty(&self, var: Variable) -> ColumnTy {
        if let Some(info) = self.vars.get(var) {
            info.ty
        } else if let Some(query) = &self.query {
            *query.var_info[var].ty()
        } else {
            panic!("unknown variable {var:?}")
        }
    }

    fn validate_args(
        &self,
        args: &[QueryEntry],
        schema: &Schema,
        arity_err: impl FnOnce(usize, usize) -> RuleError,
        type_err: impl FnOnce(ColumnTy, ColumnTy) -> RuleError,
    ) -> Result<()> {
        if args.len() != schema.arity() {
            return Err(arity_err(schema.arity(), args.len()).into());
        }

        for (entry, expected) in args.iter().zip(schema.args().iter()) {
            match entry {
                QueryEntry::Var(var) => {
                    let var_ty = self.get_ty(*var);
                    if var_ty != *expected {
                        return Err(type_err(*expected, var_ty).into());
                    }
                }
                QueryEntry::Const(_) => {
                    // NB: we currently do no validation for constant arguments
                    // to actions. This is something we could address by looking
                    // for the value in the primitives database, but we
                    // currently do not do it. This is not a safety concern, but
                    // it could be a source of panics while running a rule.
                }
            }
        }
        Ok(())
    }

    fn validate_comparison(&self, a: QueryEntry, b: QueryEntry) -> Result<()> {
        match (a, b) {
            (QueryEntry::Var(va), QueryEntry::Var(vb)) => {
                let a_ty = self.get_ty(va);
                let b_ty = self.get_ty(vb);
                if a_ty != b_ty {
                    return Err(RuleError::InvalidComparison {
                        left: a_ty,
                        right: b_ty,
                    }
                    .into());
                }
            }
            (QueryEntry::Var(_), QueryEntry::Const(_))
            | (QueryEntry::Const(_), QueryEntry::Var(_))
            | (QueryEntry::Const(_), QueryEntry::Const(_)) => {
                // See the comment in validate_args about typechecking constants.
            }
        };
        Ok(())
    }

    fn validate_func(&self, func: FunctionId, args: &[QueryEntry]) -> Result<()> {
        let schema = self.db.funcs()[func].schema();
        self.validate_args(
            args,
            schema,
            |expected, actual| RuleError::ArityMismatch {
                func,
                expected,
                actual,
            },
            |expected, actual| RuleError::FunctionTypeError {
                func,
                expected,
                actual,
            },
        )
    }

    fn validate_prim(&self, func: PrimitiveFunctionId, args: &[QueryEntry]) -> Result<()> {
        let schema = self.db.prims().get_schema(func);
        self.validate_args(
            args,
            &schema,
            |expected, actual| RuleError::PrimitiveArityMismatch {
                func,
                expected,
                actual,
            },
            |expected, actual| RuleError::PrimitiveTypeError {
                func,
                expected,
                actual,
            },
        )
    }
}

fn convert_args<'pool>(
    db: &mut Db<'pool, '_>,
    bindings: &DenseIdMap<Variable, Value>,
    args: &[QueryEntry],
) -> PoolRef<'pool, Vec<Value>> {
    let mut vals = db.pool_set().get_default::<Vec<Value>>();
    for arg in args {
        vals.push(get_val(bindings, *arg));
    }
    vals
}

fn get_val(bindings: &DenseIdMap<Variable, Value>, entry: QueryEntry) -> Value {
    match entry {
        QueryEntry::Var(v) => bindings[v],
        QueryEntry::Const(c) => c,
    }
}

pub(crate) fn run_instrs(
    bindings: &mut DenseIdMap<Variable, Value>,
    db: &mut Db,
    instrs: &[Instr],
    mut f: impl FnMut(&mut DenseIdMap<Variable, Value>),
) {
    for cur in instrs {
        match cur {
            Instr::LookupWithDefault { func, args, dst } => {
                let vals = convert_args(db, bindings, args);
                bindings.insert(*dst, db.get_with_default(*func, &vals))
            }
            Instr::Lookup { func, args, dst } => {
                let vals = convert_args(db, bindings, args);
                if let Some(res) = db.get(*func, &vals) {
                    bindings.insert(*dst, res);
                } else {
                    return;
                }
            }
            Instr::Union(l, r) => {
                db.uf().union(bindings[*l], bindings[*r]);
            }
            Instr::Insert { func, args, ret } => {
                let vals = convert_args(db, bindings, args);
                match ret {
                    QueryEntry::Var(v) => {
                        db.insert(*func, &vals, bindings[*v]);
                    }
                    QueryEntry::Const(c) => {
                        db.insert(*func, &vals, *c);
                    }
                }
            }
            Instr::Remove { func, args } => {
                let vals = convert_args(db, bindings, args);
                db.remove(*func, &vals);
            }
            Instr::Prim { func, args, dst } => {
                let vals = convert_args(db, bindings, args);
                let res = db.prims_mut().apply_op(*func, &vals);
                bindings.insert(*dst, res);
            }

            Instr::TieBreak { a, b, min, max } => {
                let a_val = bindings[*a];
                let b_val = bindings[*b];
                if a_val < b_val {
                    bindings.insert(*min, a_val);
                    bindings.insert(*max, b_val);
                } else {
                    bindings.insert(*min, b_val);
                    bindings.insert(*max, a_val);
                }
            }
            Instr::AssertEq(l, r) => {
                if get_val(bindings, *l) != get_val(bindings, *r) {
                    return;
                }
            }
            Instr::AssertNe(l, r) => {
                if get_val(bindings, *l) == get_val(bindings, *r) {
                    return;
                }
            }
        }
    }
    f(bindings)
}

#[derive(Debug)]
pub(crate) enum Instr {
    /// Look up the value of the given function, inserting a new entry with a
    /// default value if it is not there.
    LookupWithDefault {
        func: FunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Look up a value of the given function, halting execution if it is not
    /// there.
    Lookup {
        func: FunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Union the two ids.
    Union(Variable, Variable),

    /// Insert the given return value value with the provided arguments into the
    /// function.
    Insert {
        func: FunctionId,
        args: Vec<QueryEntry>,
        ret: QueryEntry,
    },

    /// Remove the entry corresponding to `args` in `func`.
    Remove {
        func: FunctionId,
        args: Vec<QueryEntry>,
    },

    /// Bind the result of a primitive function to a variable.
    Prim {
        func: PrimitiveFunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Bind `min` to the minimum of `a` and `b` and `max` to the maximum of `a`
    /// and `b`.
    ///
    /// Users can't really assume anything about the ordering of two values, but
    /// this lets them break ties in a consistent way.
    TieBreak {
        a: Variable,
        b: Variable,
        min: Variable,
        max: Variable,
    },

    /// Continue execution iff the two variables are equal.
    AssertEq(QueryEntry, QueryEntry),

    /// Continue execution iff the two variables are not equal.
    AssertNe(QueryEntry, QueryEntry),
}

//! APIs for building a query of a database.

use std::error::Error;

use thiserror::Error;

use crate::{
    action::{Instr, QueryEntry, WriteVal},
    common::{DenseIdMap, HashMap, NumericId},
    free_join::{
        plan::{Plan, PlanStrategy},
        ActionId, AtomId, ColumnTy, Database, ProcessedConstraints, SubAtom, TableId, TableInfo,
        VarInfo, Variable,
    },
    pool::Pooled,
    primitives::{PrimitiveFunctionId, PrimitiveId},
    table_spec::{ColumnId, Constraint},
};

/// A set of queries to run against a [`Database`]
#[derive(Default)]
pub struct RuleSet {
    pub(crate) plans: Vec<Plan>,
    pub(crate) actions: DenseIdMap<ActionId, Pooled<Vec<Instr>>>,
}

/// Builder for a [`RuleSet`].
///
/// See [`Database::new_rule_set`] for more information.
pub struct RuleSetBuilder<'outer> {
    rule_set: RuleSet,
    db: &'outer mut Database,
}

impl<'outer> RuleSetBuilder<'outer> {
    pub fn new(db: &'outer mut Database) -> Self {
        Self {
            rule_set: Default::default(),
            db,
        }
    }

    /// Estimate the size of the subset of the table matching the given
    /// constraint.
    pub fn estimate_size(&self, table: TableId, c: Option<Constraint>) -> usize {
        let table_info = self
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        let mut sub = table_info.table.all(self.db.pool_set());
        if let Some(c) = c {
            if let Some(sub) = table_info.table.fast_subset(&c, self.db.pool_set()) {
                return sub.size();
            }
            sub = table_info.table.refine(sub, &[c], self.db.pool_set());
        }
        sub.size()
    }

    /// Start a new query against this rule set.
    pub fn new_query<'a>(&'a mut self) -> QueryBuilder<'outer, 'a> {
        let instrs = self.db.pool_set().get();
        QueryBuilder {
            rsb: self,
            instrs,
            query: Query {
                var_info: Default::default(),
                atoms: Default::default(),
                // start with an invalid ActionId
                action: ActionId::new(u32::MAX),
            },
        }
    }

    /// Build the ruleset.
    pub fn build(self) -> RuleSet {
        self.rule_set
    }
}

/// Builder for the "query" portion of the rule.
///
/// Queries specify scans or joins over the database that bind variables that
/// are accessible to rules.
pub struct QueryBuilder<'outer, 'a> {
    rsb: &'a mut RuleSetBuilder<'outer>,
    query: Query,
    instrs: Pooled<Vec<Instr>>,
}

impl<'outer, 'a> QueryBuilder<'outer, 'a> {
    pub fn rules(self) -> RuleBuilder<'outer, 'a> {
        RuleBuilder { qb: self }
    }

    /// Create a new variable of the given type.
    pub fn new_var(&mut self, ty: ColumnTy) -> Variable {
        self.query.var_info.push(VarInfo {
            ty,
            occurrences: Default::default(),
        })
    }

    /// Add the given atom to the query, with the given variables and constraints.
    ///
    /// NB: it is possible to constrain two non-equal variables to be equal
    /// given this setup. Doing this will not cause any problems but
    /// nevertheless is not recommended.
    ///
    /// # Panics
    /// Like most methods that take a [`TableId`], this method will panic if the
    /// given table is not declared in the corresponding database.
    pub fn add_atom(
        &mut self,
        table_id: TableId,
        vars: &[Variable],
        cs: &[Constraint],
    ) -> Result<(), impl Error> {
        let arity = self.rsb.db.tables[table_id].types.len();
        let check_constraint = |c: &Constraint| {
            let process_col = |col: &ColumnId| -> Result<(), QueryError> {
                if col.index() >= arity {
                    Err(QueryError::InvalidConstraint {
                        constraint: c.clone(),
                        column: col.index(),
                        table: table_id,
                        arity,
                    })
                } else {
                    Ok(())
                }
            };
            match c {
                Constraint::Eq { l_col, r_col } => {
                    process_col(l_col)?;
                    process_col(r_col)
                }
                Constraint::EqConst { col, .. }
                | Constraint::LtConst { col, .. }
                | Constraint::GtConst { col, .. }
                | Constraint::LeConst { col, .. }
                | Constraint::GeConst { col, .. } => process_col(col),
            }
        };
        cs.iter().try_fold((), |_, c| check_constraint(c))?;
        if arity != vars.len() {
            return Err(QueryError::BadArity {
                table: table_id,
                expected: arity,
                got: vars.len(),
            });
        }
        let processed = self.rsb.db.process_constraints(table_id, cs);
        let mut atom = Atom {
            table: table_id,
            var_to_column: Default::default(),
            column_to_var: Default::default(),
            constraints: processed,
        };
        let next_atom = AtomId::from_usize(self.query.atoms.n_ids());
        let mut subatoms = HashMap::<Variable, SubAtom>::default();
        for (i, var) in vars.iter().enumerate() {
            let ty = self.query.var_info[*var].ty;
            if ty != self.rsb.db.tables[table_id].types[i] {
                return Err(QueryError::InvalidType {
                    var: *var,
                    expected: self.rsb.db.tables[table_id].types[i],
                    found: ty,
                });
            }
            let col = ColumnId::from_usize(i);
            if let Some(prev) = atom.var_to_column.insert(*var, col) {
                atom.constraints.slow.push(Constraint::Eq {
                    l_col: col,
                    r_col: prev,
                })
            };
            atom.column_to_var.insert(col, *var);
            subatoms
                .entry(*var)
                .or_insert_with(|| SubAtom::new(next_atom))
                .vars
                .push(col);
        }
        for (var, subatom) in subatoms {
            self.query
                .var_info
                .get_mut(var)
                .expect("all variables must be bound in current query")
                .occurrences
                .push(subatom);
        }
        self.query.atoms.push(atom);
        Ok(())
    }
}

#[derive(Debug, Error)]
pub enum RuleError {
    #[error(
        "variable {var:?} declared as {declared:?} but used as {column_id:?} in table {table:?}"
    )]
    TypeMismatch {
        var: Variable,
        declared: ColumnTy,
        column_id: ColumnId,
        used_as: ColumnTy,
        table: TableId,
    },
    #[error("table {table:?} has {expected:?} keys but got {got:?}")]
    KeyArityMismatch {
        table: TableId,
        expected: usize,
        got: usize,
    },
    #[error("table {table:?} has {expected:?} columns but got {got:?}")]
    TableArityMismatch {
        table: TableId,
        expected: usize,
        got: usize,
    },

    #[error("counter used in primitive column {column_id:?} of table {table:?}, which is declared as a primitive")]
    CounterUsedInPrimitiveColumn {
        table: TableId,
        column_id: ColumnId,
        prim: PrimitiveId,
    },

    #[error("invalid comparison between variable {v1:?} of type {ty1:?} and variable {v2:?} of type {ty2:?}")]
    InvalidComparison {
        v1: Variable,
        ty1: ColumnTy,
        v2: Variable,
        ty2: ColumnTy,
    },

    #[error("primitive {prim:?} expects {expected:?} arguments but got {got:?}")]
    PrimitiveArityMismatch {
        prim: PrimitiveFunctionId,
        expected: usize,
        got: usize,
    },

    #[error(
        "primitive {prim:?} expects argument {arg:?} to be of type {expected:?} but got {got:?}"
    )]
    PrimitiveTypeMismatch {
        prim: PrimitiveFunctionId,
        arg: usize,
        expected: PrimitiveId,
        got: ColumnTy,
    },

    #[error("attempt to compare two groups of values, one of length {l}, another of length {r}")]
    MultiComparisonMismatch { l: usize, r: usize },
}

#[derive(Debug, Error)]
pub(crate) enum QueryError {
    #[error("variable {var:?} has type {found:?} but was expected to have type {expected:?}")]
    InvalidType {
        var: Variable,
        expected: ColumnTy,
        found: ColumnTy,
    },

    #[error("table {table:?} expected {expected:?} columns but got {got:?}")]
    BadArity {
        table: TableId,
        expected: usize,
        got: usize,
    },

    #[error("expected {expected:?} columns in schema but got {got:?}")]
    InvalidSchema { expected: usize, got: usize },

    #[error("constraint {constraint:?} on table {table:?} references column {column:?}, but the table has arity {arity:?}")]
    InvalidConstraint {
        constraint: Constraint,
        column: usize,
        table: TableId,
        arity: usize,
    },
}

pub struct RuleBuilder<'outer, 'a> {
    qb: QueryBuilder<'outer, 'a>,
}

impl<'outer, 'a> RuleBuilder<'outer, 'a> {
    /// Build the finished query.
    pub fn build(mut self) {
        // Generate an id for our actions and slot them in.
        let action_id = self.qb.rsb.rule_set.actions.push(self.qb.instrs);
        self.qb.query.action = action_id;
        // Plan the query
        let plan = self
            .qb
            .rsb
            .db
            .plan_query(self.qb.query, PlanStrategy::MinCover);
        // Add it to the ruleset.
        self.qb.rsb.rule_set.plans.push(plan);
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, the values
    /// specified by `default_vals` will be inserted.
    pub fn lookup_or_insert(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        default_vals: &[WriteVal],
        dst_col: ColumnId,
    ) -> Result<Variable, RuleError> {
        let table_info = self
            .qb
            .rsb
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        self.validate_keys(table, table_info, args)?;
        self.validate_vals(table, table_info, default_vals.iter())?;
        let dst_ty = table_info.types[dst_col.index()];
        let res = self.qb.new_var(dst_ty);
        self.qb.instrs.push(Instr::LookupOrInsertDefault {
            table,
            args: args.to_vec(),
            default: default_vals.to_vec(),
            dst_col,
            dst_var: res,
        });
        Ok(res)
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, the variable
    /// takes the value of `default`.
    pub fn lookup_with_default(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        default: QueryEntry,
        dst_col: ColumnId,
    ) -> Result<Variable, RuleError> {
        let table_info = self
            .qb
            .rsb
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        self.validate_keys(table, table_info, args)?;
        if let (QueryEntry::Var(v), ty) = (default, table_info.types[dst_col.index()]) {
            let declared_as = self.qb.query.var_info[v].ty();
            if declared_as != ty {
                return Err(RuleError::TypeMismatch {
                    var: v,
                    declared: declared_as,
                    column_id: dst_col,
                    used_as: ty,
                    table,
                });
            }
        }
        let dst_ty = table_info.types[dst_col.index()];
        let res = self.qb.new_var(dst_ty);
        self.qb.instrs.push(Instr::LookupWithDefault {
            table,
            args: args.to_vec(),
            dst_col,
            dst_var: res,
            default,
        });
        Ok(res)
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, execution of
    /// the rule is halted.
    pub fn lookup(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        dst_col: ColumnId,
    ) -> Result<Variable, RuleError> {
        let table_info = self
            .qb
            .rsb
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        self.validate_keys(table, table_info, args)?;
        let dst_ty = table_info.types[dst_col.index()];
        let res = self.qb.new_var(dst_ty);
        self.qb.instrs.push(Instr::Lookup {
            table,
            args: args.to_vec(),
            dst_col,
            dst_var: res,
        });
        Ok(res)
    }

    /// Insert the specified values into the given table.
    pub fn insert(&mut self, table: TableId, vals: &[QueryEntry]) -> Result<(), RuleError> {
        let table_info = self
            .qb
            .rsb
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        self.validate_row(table, table_info, vals)?;
        self.qb.instrs.push(Instr::Insert {
            table,
            vals: vals.to_vec(),
        });
        Ok(())
    }

    /// Remove the specified entry from the given table, if it is there.
    pub fn remove(&mut self, table: TableId, args: &[QueryEntry]) -> Result<(), RuleError> {
        let table_info = self
            .qb
            .rsb
            .db
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        self.validate_keys(table, table_info, args)?;
        self.qb.instrs.push(Instr::Remove {
            table,
            args: args.to_vec(),
        });
        Ok(())
    }

    /// Apply the given primitive function to the specified arguments.
    pub fn prim(
        &mut self,
        prim_func: PrimitiveFunctionId,
        args: &[QueryEntry],
    ) -> Result<Variable, RuleError> {
        let (arg_tys, ret_ty) = self.qb.rsb.db.primitives().get_schema(prim_func);
        if args.len() != arg_tys.len() {
            return Err(RuleError::PrimitiveArityMismatch {
                prim: prim_func,
                expected: arg_tys.len(),
                got: args.len(),
            });
        }
        for (i, (arg, ty)) in args.iter().zip(arg_tys.iter()).enumerate() {
            let col_ty = ColumnTy::Primitive(*ty);
            match arg {
                QueryEntry::Var(v) => {
                    let declared_as = self.qb.query.var_info[*v].ty();

                    if declared_as != col_ty {
                        return Err(RuleError::PrimitiveTypeMismatch {
                            prim: prim_func,
                            arg: i,
                            expected: *ty,
                            got: declared_as,
                        });
                    }
                }
                QueryEntry::Const(_) => {}
            }
        }
        let res = self.qb.new_var(ColumnTy::Primitive(ret_ty));
        self.qb.instrs.push(Instr::Prim {
            table: prim_func,
            args: args.to_vec(),
            dst: res,
        });
        Ok(res)
    }

    /// Continue execution iff the two arguments are equal.
    pub fn assert_eq(&mut self, l: QueryEntry, r: QueryEntry) -> Result<(), RuleError> {
        match (&l, &r) {
            (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                let ty1 = self.qb.query.var_info[*v1].ty();
                let ty2 = self.qb.query.var_info[*v2].ty();
                if ty1 != ty2 {
                    return Err(RuleError::InvalidComparison {
                        v1: *v1,
                        ty1,
                        v2: *v2,
                        ty2,
                    });
                }
            }
            (QueryEntry::Var(_), QueryEntry::Const(_))
            | (QueryEntry::Const(_), QueryEntry::Var(_))
            | (QueryEntry::Const(_), QueryEntry::Const(_)) => {}
        }
        self.qb.instrs.push(Instr::AssertEq(l, r));
        Ok(())
    }

    /// Continue execution iff the two arguments are not equal.
    pub fn assert_ne(&mut self, l: QueryEntry, r: QueryEntry) -> Result<(), RuleError> {
        match (&l, &r) {
            (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                let ty1 = self.qb.query.var_info[*v1].ty();
                let ty2 = self.qb.query.var_info[*v2].ty();
                if ty1 != ty2 {
                    return Err(RuleError::InvalidComparison {
                        v1: *v1,
                        ty1,
                        v2: *v2,
                        ty2,
                    });
                }
            }
            (QueryEntry::Var(_), QueryEntry::Const(_))
            | (QueryEntry::Const(_), QueryEntry::Var(_))
            | (QueryEntry::Const(_), QueryEntry::Const(_)) => {}
        }
        self.qb.instrs.push(Instr::AssertNe(l, r));
        Ok(())
    }

    /// Continue execution iff there is some i such that l[i] != r[i].
    ///
    /// This is useful when doing egglog-style rebuilding.
    pub fn assert_any_ne(&mut self, l: &[QueryEntry], r: &[QueryEntry]) -> Result<(), RuleError> {
        if l.len() != r.len() {
            return Err(RuleError::MultiComparisonMismatch {
                l: l.len(),
                r: r.len(),
            });
        }

        for (l, r) in l.iter().zip(r.iter()) {
            if let (QueryEntry::Var(v1), QueryEntry::Var(v2)) = (l, r) {
                let ty1 = self.qb.query.var_info[*v1].ty();
                let ty2 = self.qb.query.var_info[*v2].ty();
                if ty1 != ty2 {
                    return Err(RuleError::InvalidComparison {
                        v1: *v1,
                        ty1,
                        v2: *v2,
                        ty2,
                    });
                }
            }
        }
        let mut ops = Vec::with_capacity(l.len() + r.len());
        ops.extend_from_slice(l);
        ops.extend_from_slice(r);
        self.qb.instrs.push(Instr::AssertAnyNe {
            ops,
            divider: l.len(),
        });
        Ok(())
    }

    fn validate_row(
        &self,
        table: TableId,
        info: &TableInfo,
        vals: &[QueryEntry],
    ) -> Result<(), RuleError> {
        if vals.len() != info.spec.arity() {
            return Err(RuleError::TableArityMismatch {
                table,
                expected: info.spec.arity(),
                got: vals.len(),
            });
        }
        for (i, val) in vals.iter().enumerate() {
            let ty = info.types[i];
            match val {
                QueryEntry::Var(v) => {
                    let expected = self.qb.query.var_info[*v].ty();
                    if expected != ty {
                        return Err(RuleError::TypeMismatch {
                            var: *v,
                            declared: expected,
                            column_id: ColumnId::from_usize(i),
                            used_as: ty,
                            table,
                        });
                    }
                }
                QueryEntry::Const(_) => {}
            }
        }
        Ok(())
    }

    fn validate_keys(
        &self,
        table: TableId,
        info: &TableInfo,
        keys: &[QueryEntry],
    ) -> Result<(), RuleError> {
        if keys.len() != info.spec.n_keys {
            return Err(RuleError::KeyArityMismatch {
                table,
                expected: info.spec.n_keys,
                got: keys.len(),
            });
        }
        for (i, key) in keys.iter().enumerate() {
            let ty = info.types[i];
            match key {
                QueryEntry::Var(v) => {
                    let expected = self.qb.query.var_info[*v].ty();
                    if expected != ty {
                        return Err(RuleError::TypeMismatch {
                            var: *v,
                            declared: expected,
                            column_id: ColumnId::from_usize(i),
                            used_as: ty,
                            table,
                        });
                    }
                }
                QueryEntry::Const(_) => {}
            }
        }
        Ok(())
    }

    fn validate_vals<'b>(
        &self,
        table: TableId,
        info: &TableInfo,
        vals: impl Iterator<Item = &'b WriteVal>,
    ) -> Result<(), RuleError> {
        for (i, val) in vals.enumerate() {
            let col = i + info.spec.n_keys;
            if col >= info.types.len() {
                return Err(RuleError::TableArityMismatch {
                    table,
                    expected: info.types.len(),
                    got: col,
                });
            }
            let ty = info.types[col];
            match val {
                WriteVal::Counter(_) => match ty {
                    ColumnTy::Id => {}
                    ColumnTy::Primitive(prim) => {
                        return Err(RuleError::CounterUsedInPrimitiveColumn {
                            table,
                            column_id: ColumnId::from_usize(col),
                            prim,
                        })
                    }
                },
                WriteVal::QueryEntry(QueryEntry::Var(v)) => {
                    let expected = self.qb.query.var_info[*v].ty();
                    if expected != ty {
                        return Err(RuleError::TypeMismatch {
                            var: *v,
                            declared: expected,
                            column_id: ColumnId::from_usize(col),
                            used_as: ty,
                            table,
                        });
                    }
                }
                WriteVal::QueryEntry(QueryEntry::Const(_)) => {}
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Atom {
    pub(crate) table: TableId,
    pub(crate) var_to_column: HashMap<Variable, ColumnId>,
    pub(crate) column_to_var: DenseIdMap<ColumnId, Variable>,
    pub(crate) constraints: ProcessedConstraints,
}

pub(crate) struct Query {
    pub(crate) var_info: DenseIdMap<Variable, VarInfo>,
    pub(crate) atoms: DenseIdMap<AtomId, Atom>,
    pub(crate) action: ActionId,
}

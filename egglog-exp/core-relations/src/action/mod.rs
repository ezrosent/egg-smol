//! Instructions that are executed on the results of a query.
//!
//! This allows us to execute the "right-hand-side" of a rule. The
//! implementation here is optimized to execute on a batch of rows at a time.
use std::rc::Rc;

use numeric_id::{DenseIdMap, NumericId};
use smallvec::SmallVec;

use crate::{
    common::{HashMap, Value},
    free_join::{inc_counter, CounterId, Database, TableId, Variable},
    pool::{PoolSet, Pooled},
    primitives::PrimitiveFunctionId,
    table_spec::ColumnId,
    ExternalFunctionId,
};

use self::mask::{Mask, MaskIter, ValueSource};

pub(crate) mod mask;

#[cfg(test)]
mod tests;

/// A representation of a value within a query or rule.
///
/// A QueryEntry is either a variable bound in a join, or an untyped constant.
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

/// A value that can be written to a table in an action.
#[derive(Debug, Clone, Copy)]
pub enum WriteVal {
    /// A variable or a constant.
    QueryEntry(QueryEntry),
    /// A fresh value from the given counter.
    IncCounter(CounterId),
    /// The value of the current row index.
    CurrentVal(usize),
}

impl<T> From<T> for WriteVal
where
    T: Into<QueryEntry>,
{
    fn from(val: T) -> Self {
        WriteVal::QueryEntry(val.into())
    }
}

impl From<CounterId> for WriteVal {
    fn from(ctr: CounterId) -> Self {
        WriteVal::IncCounter(ctr)
    }
}

/// A value that can be written to the database during a merge action.
#[derive(Debug, Copy, Clone)]
pub enum MergeVal {
    /// A fresh value from the given counter.
    Counter(CounterId),
    /// A standard constant value.
    Constant(Value),
}

impl From<CounterId> for MergeVal {
    fn from(ctr: CounterId) -> Self {
        MergeVal::Counter(ctr)
    }
}

impl From<Value> for MergeVal {
    fn from(val: Value) -> Self {
        MergeVal::Constant(val)
    }
}

pub(crate) type Bindings = DenseIdMap<Variable, Pooled<Vec<Value>>>;

#[derive(Default)]
pub(crate) struct PredictedVals {
    #[allow(clippy::type_complexity)]
    data: HashMap<(TableId, SmallVec<[Value; 3]>), Pooled<Rc<Vec<Value>>>>,
}

impl PredictedVals {
    pub(crate) fn get_val(
        &mut self,
        table: TableId,
        key: &[Value],
        default: impl FnOnce() -> Pooled<Rc<Vec<Value>>>,
    ) -> &Pooled<Rc<Vec<Value>>> {
        self.data
            .entry((table, SmallVec::from_slice(key)))
            .or_insert_with(default)
    }
}

pub struct ExecutionState<'a> {
    pub(crate) predicted: &'a mut PredictedVals,
    pub(crate) db: &'a mut Database,
}

impl<'a> ExecutionState<'a> {
    pub fn pool_set(&self) -> &PoolSet {
        &self.db.pool_set
    }
    pub(crate) fn run_instrs(&mut self, instrs: &[Instr], bindings: &mut Bindings) {
        let Some(batch_size) = bindings.iter().map(|(_, x)| x.len()).next() else {
            // Empty bindings; nothing to do.
            return;
        };
        let mut mask = Mask::new(0..batch_size, self.db.pool_set.get_pool());
        for instr in instrs {
            if mask.is_empty() {
                break;
            }
            self.run_instr(&mut mask, instr, bindings);
        }
    }

    pub(crate) fn merge_all(&mut self) -> bool {
        let mut ever_changed = false;
        loop {
            let mut changed = false;
            for id in 0..self.db.tables.n_ids() {
                // Move the table out of the tables map. Run the merge (which can
                // access the rest of the db). Then put it back.
                let table = TableId::from_usize(id);
                let mut info = self.db.tables.take(table);
                let table_changed = info.table.merge(self);
                changed |= table_changed;
                self.db.tables.insert(table, info);
            }
            ever_changed |= changed;
            if !changed {
                break;
            }
        }
        ever_changed
    }

    pub(crate) fn merge_table(&mut self, table: TableId) {
        let mut info = self.db.tables.take(table);
        let _table_changed = info.table.merge(self);
        self.db.tables.insert(table, info);
    }

    pub fn stage_insert(&mut self, table: TableId, vals: &[Value]) {
        self.db.get_table_mut(table).stage_insert(vals);
    }
    pub fn stage_remove(&mut self, table: TableId, vals: &[Value]) {
        self.db.get_table_mut(table).stage_remove(vals);
    }

    /// Get the _current_ value for a given key in `table`, or otherwise insert
    /// the unique _next_ value.
    ///
    /// Insertions into tables are not performed immediately, but rules and
    /// merge functions sometimes need to get the result of an insertion. For
    /// such cases, executions keep a cache of "predicted" values for a given
    /// mapping that manage the insertions, etc.
    pub fn predict_val(
        &mut self,
        table: TableId,
        key: &[Value],
        vals: impl ExactSizeIterator<Item = MergeVal>,
    ) -> Pooled<Rc<Vec<Value>>> {
        if let Some(row) = self.db.get_table(table).get_row(key, self.db.pool_set()) {
            return Pooled::transfer_rc(row.vals, self.db.pool_set.get_pool());
        }
        self.predicted
            .get_val(table, key, || {
                let mut new = self.db.pool_set.get::<Rc<Vec<Value>>>();
                let new_mut = Rc::get_mut(&mut new).unwrap();
                new_mut.reserve(key.len() + vals.len());
                new_mut.extend_from_slice(key);
                for val in vals {
                    new_mut.push(match val {
                        MergeVal::Counter(ctr) => Value::from_usize(self.db.inc_counter(ctr)),
                        MergeVal::Constant(c) => c,
                    })
                }
                self.db.get_table_mut(table).stage_insert(&new);
                new
            })
            .clone()
    }
    fn run_instr(&mut self, mask: &mut Mask, inst: &Instr, bindings: &mut Bindings) {
        fn assert_impl(
            bindings: &mut Bindings,
            mask: &mut Mask,
            l: &QueryEntry,
            r: &QueryEntry,
            op: impl Fn(Value, Value) -> bool,
        ) {
            match (l, r) {
                (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                    mask.iter(&bindings[*v1])
                        .zip(&bindings[*v2])
                        .retain(|(v1, v2)| op(*v1, *v2));
                }
                (QueryEntry::Var(v), QueryEntry::Const(c))
                | (QueryEntry::Const(c), QueryEntry::Var(v)) => {
                    mask.iter(&bindings[*v]).retain(|v| op(*v, *c));
                }
                (QueryEntry::Const(c1), QueryEntry::Const(c2)) => {
                    if !op(*c1, *c2) {
                        mask.clear();
                    }
                }
            }
        }

        // Helper macro for taking a slice of QueryEntries and creating a call
        // to `iter_dynamic` on `mask`.
        //
        // `iter_dynamic` takes a dynamically-determined number of "value
        // sources" (either a slice or a constant) and then does a masked
        // iteration on the "transpose" of these sources (row-wise).
        macro_rules! iter_entries {
            ($pool:expr, $entries:expr) => {
                mask.iter_dynamic(
                    $pool,
                    $entries.iter().map(|v| match v {
                        QueryEntry::Var(v) => {
                            debug_assert!(
                                bindings.get(*v).is_some(),
                                "variable {:?} not found in bindings {:?}",
                                v,
                                bindings
                            );
                            ValueSource::Slice(&bindings[*v])
                        }
                        QueryEntry::Const(c) => ValueSource::Const(*c),
                    }),
                )
            };
        }
        match inst {
            Instr::LookupOrInsertDefault {
                table: table_id,
                args,
                default,
                dst_col,
                dst_var,
            } => {
                // use the raw fields becaust `table` must be mutable, and we
                // also need pool_set.
                let pool_set = &self.db.pool_set;
                let shared_pool = pool_set.get_pool::<Rc<Vec<Value>>>().clone();
                let pool = pool_set.get_pool::<Vec<Value>>().clone();
                let mut table = self.db.tables.get_mut(*table_id).unwrap().table_mut();
                let mut out = pool.get();

                // TODO: we may want to vectorize this one better: do a round of
                // lookups, then for ones that failed, do a round of inserts.
                iter_entries!(pool, args).fill_vec(&mut out, Value::stale, |offset, key| {
                    // First, check if the entry is already in the table:
                    if let Some(row) = table.get_row_column(&key, *dst_col, pool_set) {
                        return Some(row);
                    }
                    // If not, insert the default value.
                    //
                    // We avoid doing this more than once by using the
                    // `predicted` map.
                    let prediction_key = (*table_id, SmallVec::<[Value; 3]>::from_slice(&key));
                    // Bind some mutable references because the closure passed
                    // to or_insert_with is `move`.
                    let ctrs = &mut self.db.counters;
                    let table = &mut table;
                    let bindings = &bindings;
                    let pool_ref = &shared_pool;
                    let row = self
                        .predicted
                        .data
                        .entry(prediction_key)
                        .or_insert_with(move || {
                            let mut row = Pooled::transfer_rc(key, pool_ref);
                            // Extend the key with the default values.
                            let row_mut = Rc::get_mut(&mut row).unwrap();
                            row_mut.reserve(default.len());
                            for val in default {
                                let val = match val {
                                    WriteVal::QueryEntry(QueryEntry::Const(c)) => *c,
                                    WriteVal::QueryEntry(QueryEntry::Var(v)) => {
                                        bindings[*v][offset]
                                    }
                                    WriteVal::IncCounter(ctr) => {
                                        Value::from_usize(inc_counter(ctrs, *ctr))
                                    }
                                    WriteVal::CurrentVal(ix) => row_mut[*ix],
                                };
                                row_mut.push(val)
                            }
                            // Insert it into the table.
                            table.stage_insert(&row);
                            row
                        });
                    Some(row[dst_col.index()])
                });
                bindings.insert(*dst_var, out);
            }
            Instr::LookupWithDefault {
                table,
                args,
                dst_col,
                dst_var,
                default,
            } => {
                let table = self.db.get_table(*table);
                table.lookup_with_default_vectorized(
                    &self.db.pool_set,
                    mask,
                    bindings,
                    args,
                    *dst_col,
                    *default,
                    *dst_var,
                );
            }
            Instr::Lookup {
                table,
                args,
                dst_col,
                dst_var,
            } => {
                let table = self.db.get_table(*table);
                table.lookup_row_vectorized(
                    &self.db.pool_set,
                    mask,
                    bindings,
                    args,
                    *dst_col,
                    *dst_var,
                );
            }
            Instr::Insert { table, vals } => {
                let pool = self.db.pool_set().get_pool::<Vec<Value>>().clone();
                let table = self.db.get_table_mut(*table);
                iter_entries!(pool, vals).for_each(|vals| {
                    table.stage_insert(&vals);
                })
            }
            Instr::InsertIfEq { table, l, r, vals } => {
                let pool = self.db.pool_set().get_pool::<Vec<Value>>().clone();
                match (l, r) {
                    (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                        let table = self.db.get_table_mut(*table);
                        iter_entries!(pool, vals)
                            .zip(&bindings[*v1])
                            .zip(&bindings[*v2])
                            .for_each(|((vals, v1), v2)| {
                                if v1 == v2 {
                                    table.stage_insert(&vals);
                                }
                            })
                    }
                    (QueryEntry::Var(v), QueryEntry::Const(c))
                    | (QueryEntry::Const(c), QueryEntry::Var(v)) => {
                        let table = self.db.get_table_mut(*table);
                        iter_entries!(pool, vals)
                            .zip(&bindings[*v])
                            .for_each(|(vals, cond)| {
                                if cond == c {
                                    table.stage_insert(&vals);
                                }
                            })
                    }
                    (QueryEntry::Const(c1), QueryEntry::Const(c2)) => {
                        if c1 == c2 {
                            let table = self.db.get_table_mut(*table);
                            iter_entries!(pool, vals).for_each(|vals| {
                                table.stage_insert(&vals);
                            })
                        }
                    }
                }
            }
            Instr::Remove { table, args } => {
                let pool = self.db.pool_set().get_pool::<Vec<Value>>().clone();
                let table = self.db.get_table_mut(*table);
                iter_entries!(pool, args).for_each(|args| {
                    table.stage_remove(&args);
                })
            }
            Instr::Prim { func, args, dst } => {
                let pool = self.db.pool_set().get_pool::<Vec<Value>>().clone();
                let prims = self.db.primitives_mut();
                prims.apply_vectorized(*func, pool, mask, bindings, args, *dst);
            }
            Instr::External { func, args, dst } => {
                let imp = self.db.extract_external_func(*func);
                imp.invoke_batch(self, mask, bindings, args, *dst);
                self.db.replace_external_func(*func, imp)
            }
            Instr::AssertAnyNe { ops, divider } => {
                let pool = self.db.pool_set().get_pool::<Vec<Value>>().clone();
                iter_entries!(pool, ops).retain(|vals| {
                    vals[0..*divider]
                        .iter()
                        .zip(&vals[*divider..])
                        .any(|(l, r)| l != r)
                })
            }
            Instr::AssertEq(l, r) => assert_impl(bindings, mask, l, r, |l, r| l == r),
            Instr::AssertNe(l, r) => assert_impl(bindings, mask, l, r, |l, r| l != r),
        }
    }
}

#[derive(Debug)]
pub(crate) enum Instr {
    /// Look up the value of the given table, inserting a new entry with a
    /// default value if it is not there.
    LookupOrInsertDefault {
        table: TableId,
        args: Vec<QueryEntry>,
        default: Vec<WriteVal>,
        dst_col: ColumnId,
        dst_var: Variable,
    },

    /// Look up the value of the given table; if the value is not there, use the
    /// given default.
    LookupWithDefault {
        table: TableId,
        args: Vec<QueryEntry>,
        dst_col: ColumnId,
        dst_var: Variable,
        default: QueryEntry,
    },

    /// Look up a value of the given table, halting execution if it is not
    /// there.
    Lookup {
        table: TableId,
        args: Vec<QueryEntry>,
        dst_col: ColumnId,
        dst_var: Variable,
    },

    /// Insert the given return value value with the provided arguments into the
    /// table.
    Insert {
        table: TableId,
        vals: Vec<QueryEntry>,
    },

    /// Insert `vals` into `table` if `l` and `r` are equal.
    InsertIfEq {
        table: TableId,
        l: QueryEntry,
        r: QueryEntry,
        vals: Vec<QueryEntry>,
    },

    /// Remove the entry corresponding to `args` in `func`.
    Remove {
        table: TableId,
        args: Vec<QueryEntry>,
    },

    /// Bind the result of a primitive function to a variable.
    Prim {
        func: PrimitiveFunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Bind the result of the external function to a variable.
    External {
        func: ExternalFunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Continue execution iff the two variables are equal.
    AssertEq(QueryEntry, QueryEntry),

    /// Continue execution iff the two variables are not equal.
    AssertNe(QueryEntry, QueryEntry),

    /// For the two slices: ops[0..divider] and ops[divider..], continue
    /// execution iff there is one pair of values at the same offset that are
    /// not equal.
    AssertAnyNe {
        ops: Vec<QueryEntry>,
        divider: usize,
    },
}

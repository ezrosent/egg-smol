//! Execute queries against a database using a variant of Free Join.
use std::{cell::RefCell, rc::Rc};

use numeric_id::{define_id, DenseIdMap};
use smallvec::SmallVec;

use crate::{
    action::{
        mask::{Mask, MaskIter, ValueSource},
        Bindings,
    },
    common::HashMap,
    hash_index::{ColumnIndex, Index},
    offsets::Subset,
    pool::{Pool, PoolSet, Pooled},
    primitives::Primitives,
    query::{Query, RuleSetBuilder},
    table_spec::{ColumnId, Constraint, Table, TableSpec, WrappedTable},
    QueryEntry, TupleIndex, Value,
};

use self::plan::Plan;
use crate::action::{ExecutionState, PredictedVals};

pub(crate) mod execute;
pub(crate) mod plan;

define_id!(
    pub(crate) AtomId,
    u32,
    "A component of a query consisting of a function and a list of variables or constants"
);
define_id!(pub Variable, u32, "a variable in a query");

impl Variable {
    pub fn placeholder() -> Variable {
        Variable::new(!0)
    }
}

define_id!(pub TableId, u32, "a table in the database");
define_id!(pub(crate) ActionId, u32, "an identifier picking out the RHS of a rule");

#[derive(Debug)]
pub(crate) struct ProcessedConstraints {
    /// The subset of the table matching the fast constraints. If there are no
    /// fast constraints then this is the full table.
    pub(crate) subset: Subset,
    /// The constraints that can be evaluated quickly (O(log(n)) or O(1)).
    pub(crate) fast: Pooled<Vec<Constraint>>,
    /// The constraints that require an O(n) scan to evaluate.
    pub(crate) slow: Pooled<Vec<Constraint>>,
}

impl Clone for ProcessedConstraints {
    fn clone(&self) -> Self {
        ProcessedConstraints {
            subset: self.subset.clone(),
            fast: Pooled::cloned(&self.fast),
            slow: Pooled::cloned(&self.slow),
        }
    }
}

impl ProcessedConstraints {
    /// The size of the subset of the table matching the fast constraints.
    fn approx_size(&self) -> usize {
        self.subset.size()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SubAtom {
    pub(crate) atom: AtomId,
    pub(crate) vars: SmallVec<[ColumnId; 2]>,
}

impl SubAtom {
    pub(crate) fn new(atom: AtomId) -> SubAtom {
        SubAtom {
            atom,
            vars: Default::default(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct VarInfo {
    pub(crate) occurrences: Vec<SubAtom>,
    /// Whether or not this variable shows up in the "actions" portion of a
    /// rule.
    pub(crate) used_in_rhs: bool,
}

pub(crate) type HashIndex = Rc<RefCell<Index<TupleIndex>>>;
pub(crate) type HashColumnIndex = Rc<RefCell<Index<ColumnIndex>>>;

pub(crate) struct TableInfo {
    pub(crate) spec: TableSpec,
    pub(crate) table: WrappedTable,
    pub(crate) indexes: HashMap<SmallVec<[ColumnId; 4]>, HashIndex>,
    pub(crate) column_indexes: HashMap<ColumnId, HashColumnIndex>,
}

impl Clone for TableInfo {
    fn clone(&self) -> Self {
        TableInfo {
            spec: self.spec.clone(),
            table: self.table.dyn_clone(),
            indexes: self.indexes.clone(),
            column_indexes: self.column_indexes.clone(),
        }
    }
}

impl TableInfo {
    pub(crate) fn table_mut(&mut self) -> &mut dyn Table {
        &mut *self.table
    }
}

define_id!(pub CounterId, u32, "A counter accessible to actions, useful for generating unique Ids.");
define_id!(pub ExternalFunctionId, u32, "A user-defined operation that can be invoked from a query");

/// External functions allow external callers to manipulate database state in
/// near-arbitrary ways.
///
/// This is a useful, if low-level, interface for extending this database with
/// functionality and state not built into the core model.
pub trait ExternalFunction {
    /// Invoke the function with mutable access to the database. If a value is
    /// not returned, halt the execution of the current rule.
    fn invoke(&self, state: &mut ExecutionState, args: &[Value]) -> Option<Value>;
}

pub(crate) trait ExternalFunctionExt: ExternalFunction {
    /// A vectorized variant of `invoke` to avoid repeated dynamic dispatch.
    ///
    /// Implementors should not override this manually (in fact, they shouldn't
    /// even be able to; some types are private); the default implementation
    /// delegates core logic to `invoke`.
    #[doc(hidden)]
    fn invoke_batch(
        &self,
        state: &mut ExecutionState,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        out_var: Variable,
    ) {
        let pool: Pool<Vec<Value>> = state.db.pool_set().get_pool().clone();
        let mut out = pool.get();
        mask.iter_dynamic(
            pool,
            args.iter().map(|v| match v {
                QueryEntry::Var(v) => ValueSource::Slice(&bindings[*v]),
                QueryEntry::Const(c) => ValueSource::Const(*c),
            }),
        )
        .fill_vec(&mut out, Value::stale, |_, args| self.invoke(state, &args));
        bindings.insert(out_var, out);
    }
}

impl<T: ExternalFunction> ExternalFunctionExt for T {}

/// A collection of tables and indexes over them.
///
/// A database also owns the memory pools used by its tables.
#[derive(Default)]
pub struct Database {
    // NB: some fields are pub(crate) to allow some internal modules to avoid
    // borrowing the whole table.
    pub(crate) tables: DenseIdMap<TableId, TableInfo>,
    pub(crate) counters: DenseIdMap<CounterId, usize>,
    pub(crate) external_functions: DenseIdMap<ExternalFunctionId, Box<dyn ExternalFunctionExt>>,
    primitives: Primitives,
    pub(crate) pool_set: PoolSet,
    stack: Vec<DbState>,
}

struct DbState {
    tables: DenseIdMap<TableId, TableInfo>,
    counters: DenseIdMap<CounterId, usize>,
}

pub(crate) fn inc_counter(
    counters: &mut DenseIdMap<CounterId, usize>,
    counter_id: CounterId,
) -> usize {
    let c = counters.get_mut(counter_id).expect("counter must exist");
    let res = *c;
    *c += 1;
    res
}

impl Database {
    /// Create an empty Database.
    pub fn new() -> Database {
        Database::default()
    }

    /// Store a snapshot of the current database state.
    ///
    /// Depending on the implementation of the tables in the database, this
    /// could deep-copy all database state.
    pub fn push(&mut self) {
        self.stack.push(DbState {
            tables: self.tables.clone(),
            counters: self.counters.clone(),
        });
    }

    /// Restore the database state to the last snapshot.
    ///
    /// # Panics
    /// This method panics if there is no state to pop.
    pub fn pop(&mut self) {
        let DbState { tables, counters } = self.stack.pop().expect("must have a state to pop");
        self.tables = tables;
        self.counters = counters;
    }

    /// Initialize a new rulse set to run against this database.
    pub fn new_rule_set(&mut self) -> RuleSetBuilder {
        RuleSetBuilder::new(self)
    }

    /// Add a new external function to the database.
    pub fn add_external_function(
        &mut self,
        f: impl ExternalFunction + 'static,
    ) -> ExternalFunctionId {
        self.external_functions.push(Box::new(f))
    }

    pub(crate) fn extract_external_func(
        &mut self,
        id: ExternalFunctionId,
    ) -> Box<dyn ExternalFunctionExt> {
        self.external_functions.take(id)
    }

    pub(crate) fn replace_external_func(
        &mut self,
        id: ExternalFunctionId,
        f: Box<dyn ExternalFunctionExt>,
    ) {
        self.external_functions.insert(id, f);
    }

    pub fn primitives(&self) -> &Primitives {
        &self.primitives
    }

    pub fn primitives_mut(&mut self) -> &mut Primitives {
        &mut self.primitives
    }

    /// Estimate the size of the table. If a constraint is provided, return an
    /// estimate of the size of the subset of the table matching the constraint.
    pub fn estimate_size(&self, table: TableId, c: Option<Constraint>) -> usize {
        let table_info = self
            .tables
            .get(table)
            .expect("table must be declared in the current database");
        let mut sub = table_info.table.all(self.pool_set());
        if let Some(c) = c {
            if let Some(sub) = table_info.table.fast_subset(&c, self.pool_set()) {
                return sub.size();
            }
            sub = table_info.table.refine(sub, &[c], self.pool_set());
        }
        sub.size()
    }

    /// Create a new counter for this database.
    ///
    /// These counters can be used to generate unique ids as part of an action.
    pub fn add_counter(&mut self) -> CounterId {
        self.counters.push(0)
    }

    pub fn pool_set(&self) -> &PoolSet {
        &self.pool_set
    }

    /// A helper for merging all pending updates. Currently only used in tests.
    ///
    /// Useful for out-of-band insertions into the database.
    pub fn merge_all(&mut self) {
        let mut predicted = PredictedVals::default();
        let mut exec_state = ExecutionState {
            db: self,
            predicted: &mut predicted,
        };
        exec_state.merge_all();
    }

    /// A low-level helper for merging pending updates to a particular function.
    ///
    /// Callers should prefer `merge_all`, as the process of merging the data
    /// for a particular table may cause other updates to be buffered
    /// elesewhere. The `merge_all` method runs merges to a fixed point to avoid
    /// surprises here.
    pub fn merge_table(&mut self, table: TableId) {
        let mut predicted = PredictedVals::default();
        let mut exec_state = ExecutionState {
            db: self,
            predicted: &mut predicted,
        };
        exec_state.merge_table(table);
    }

    /// Increment the given counter and return its previous value.
    pub fn inc_counter(&mut self, counter: CounterId) -> usize {
        inc_counter(&mut self.counters, counter)
    }

    /// Get id of the next table to be added to the database.
    ///
    /// This can be useful for "knot tying", when tables need to reference their
    /// own id.
    pub fn next_table_id(&self) -> TableId {
        self.tables.next_id()
    }

    /// Add a table with the given schema to the database.
    ///
    /// The table must have a compatible spec with `types` (e.g. same number of
    /// columns).
    pub fn add_table<T: Table + Sized + 'static>(&mut self, table: T) -> TableId {
        let spec = table.spec();
        let table = WrappedTable::new(table);
        self.tables.push(TableInfo {
            spec,
            table,
            indexes: Default::default(),
            column_indexes: Default::default(),
        })
    }

    /// Get direct mutable access to the table.
    ///
    /// This method is useful for out-of-band access to databse state.
    pub fn get_table(&self, id: TableId) -> &WrappedTable {
        &self
            .tables
            .get(id)
            .expect("must access a table that has been declared in this database")
            .table
    }

    pub(crate) fn process_constraints(
        &mut self,
        table: TableId,
        cs: &[Constraint],
    ) -> ProcessedConstraints {
        let table_info = &mut self.tables[table];
        let (mut subset, mut fast, mut slow) = table_info.table.split_fast_slow(cs, &self.pool_set);
        slow.retain(|c| {
            let (col, val) = match c {
                Constraint::EqConst { col, val } => (*col, *val),
                Constraint::Eq { .. }
                | Constraint::LtConst { .. }
                | Constraint::GtConst { .. }
                | Constraint::LeConst { .. }
                | Constraint::GeConst { .. } => return true,
            };
            // We are looking up by a constant: this is something we can build
            // an index for as long as the column is cacheable.
            if *table_info
                .spec
                .uncacheable_columns
                .get(col)
                .unwrap_or(&false)
            {
                return true;
            }
            // We have or will build an index: upgrade this constraint to
            // 'fast'.
            fast.push(c.clone());
            let index = get_column_index_from_tableinfo(table_info, col, &self.pool_set);
            match index.borrow().get_subset(&val) {
                Some(s) => {
                    subset.intersect(s, self.pool_set.get_pool());
                }
                None => {
                    // There are no rows matching this key! We can constrain this to nothing.
                    subset = Subset::empty();
                }
            }
            // Remove this constraint from the slow list.
            false
        });
        ProcessedConstraints { subset, fast, slow }
    }

    /// Get direct mutable access to the table.
    ///
    /// This method is useful for out-of-band access to databse state.
    pub fn get_table_mut(&mut self, id: TableId) -> &mut dyn Table {
        &mut *self
            .tables
            .get_mut(id)
            .expect("must access a table that has been declared in this database")
            .table
    }

    pub(crate) fn plan_query(&mut self, query: Query) -> Plan {
        plan::plan_query(query)
    }
}

/// The core logic behind getting and updating a hash index.
///
/// This is in a separate function to allow us to reuse it while already
/// borrowing a `TableInfo`.
fn get_index_from_tableinfo<'a>(
    table_info: &'a mut TableInfo,
    cols: &[ColumnId],
    pool_set: &PoolSet,
) -> &'a HashIndex {
    let (_, index) = table_info
        .indexes
        .raw_entry_mut()
        .from_key(cols)
        .or_insert_with(|| {
            (
                cols.iter().copied().collect(),
                Rc::new(RefCell::new(Index::new(
                    cols.to_vec(),
                    TupleIndex::new(cols.len(), pool_set),
                ))),
            )
        });
    if let Ok(mut ix) = index.try_borrow_mut() {
        // NB: why is try_borrow safe?
        // * We update indexes from within the execution of free join.
        // * We may use the same index more than once during a query, so
        // try_borrow_mut() can fail.
        // * But we only need to refresh the table _once_ at the beginning of
        // the query, so a single success is all we need.
        ix.refresh(&table_info.table, pool_set);
    }
    index
}

/// The core logic behind getting and updating a column index.
///
/// This is the single-column analog to [`get_index_from_tableinfo`].
fn get_column_index_from_tableinfo<'a>(
    table_info: &'a mut TableInfo,
    col: ColumnId,
    pool_set: &PoolSet,
) -> &'a HashColumnIndex {
    let index = table_info.column_indexes.entry(col).or_insert_with(|| {
        Rc::new(RefCell::new(Index::new(
            vec![col],
            ColumnIndex::new(pool_set),
        )))
    });
    if let Ok(mut ix) = index.try_borrow_mut() {
        ix.refresh(&table_info.table, pool_set);
    }
    index
}

//! Execute queries against a database using a variant of Free Join.
use std::{cell::RefCell, error::Error, rc::Rc};

use smallvec::SmallVec;

use crate::{
    common::{DenseIdMap, HashMap},
    define_id,
    hash_index::Index,
    offsets::Subset,
    pool::{PoolSet, Pooled},
    primitives::{PrimitiveId, Primitives},
    query::{Query, QueryError, RuleSetBuilder},
    table_spec::{ColumnId, Constraint, Table, TableSpec},
};

use self::plan::{Plan, PlanStrategy};
#[cfg(test)]
use crate::action::{ExecutionState, PredictedVals};

pub(crate) mod execute;
pub(crate) mod plan;
#[cfg(test)]
mod tests;

define_id!(
    pub(crate) AtomId,
    u32,
    "A component of a query consisting of a function and a list of variables or constants"
);
define_id!(pub Variable, u32, "a variable in a query");
define_id!(pub TableId, u32, "a table in the database");
define_id!(pub(crate) ActionId, u32, "an identifier picking out the RHS of a rule");

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ColumnTy {
    Id,
    Primitive(PrimitiveId),
}

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
    pub(crate) vars: SmallVec<[ColumnId; 4]>,
}

impl SubAtom {
    pub(crate) fn new(atom: AtomId) -> SubAtom {
        SubAtom {
            atom,
            vars: Default::default(),
        }
    }
}

pub(crate) struct VarInfo {
    pub(crate) ty: ColumnTy,
    pub(crate) occurrences: Vec<SubAtom>,
}

impl VarInfo {
    pub(crate) fn ty(&self) -> ColumnTy {
        self.ty
    }
}

pub(crate) type HashIndex = Rc<RefCell<Index>>;

pub(crate) struct TableInfo {
    pub(crate) types: Vec<ColumnTy>,
    pub(crate) spec: TableSpec,
    pub(crate) table: Box<dyn Table>,
    pub(crate) indexes: HashMap<SmallVec<[ColumnId; 4]>, HashIndex>,
}

impl TableInfo {
    pub(crate) fn table_mut(&mut self) -> &mut dyn Table {
        &mut *self.table
    }
}

define_id!(pub CounterId, u32, "A counter accessible to actions, useful for generating unique Ids.");

/// A collection of tables and indexes over them.
///
/// A database also owns the memory pools used by its tables.
#[derive(Default)]
pub struct Database {
    // NB: some fields are pub(crate) to allow some internal modules to avoid
    // borrowing the whole table.
    pub(crate) tables: DenseIdMap<TableId, TableInfo>,
    pub(crate) counters: DenseIdMap<CounterId, usize>,
    primitives: Primitives,
    pub(crate) pool_set: PoolSet,
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

    /// Initialize a new rulse set to run against this database.
    pub fn new_rule_set(&mut self) -> RuleSetBuilder {
        RuleSetBuilder::new(self)
    }

    pub fn primitives(&self) -> &Primitives {
        &self.primitives
    }

    pub fn primitives_mut(&mut self) -> &mut Primitives {
        &mut self.primitives
    }

    /// Create a new counter for this database.
    ///
    /// These counters can be used to generate unique ids as part of an action.
    pub fn add_counter(&mut self) -> CounterId {
        self.counters.push(0)
    }

    pub(crate) fn pool_set(&self) -> &PoolSet {
        &self.pool_set
    }

    /// A helper for merging all pending updates. Currently only used in tests.
    #[cfg(test)]
    pub(crate) fn merge_all(&mut self) {
        let mut predicted = PredictedVals::default();
        let mut exec_state = ExecutionState {
            db: self,
            predicted: &mut predicted,
        };
        exec_state.merge_all();
    }

    /// Increment the given counter and return its previous value.
    pub(crate) fn inc_counter(&mut self, counter: CounterId) -> usize {
        inc_counter(&mut self.counters, counter)
    }

    /// Add a table with the given schema to the database.
    ///
    /// The table must have a compatible spec with `types` (e.g. same number of
    /// columns).
    pub fn add_table(
        &mut self,
        types: Vec<ColumnTy>,
        table: Box<dyn Table>,
    ) -> Result<TableId, impl Error> {
        let spec = table.spec();
        let expected = spec.n_keys + spec.n_vals;
        if expected == types.len() {
            Ok(self.tables.push(TableInfo {
                types,
                spec,
                table,
                indexes: Default::default(),
            }))
        } else {
            Err(QueryError::InvalidSchema {
                expected,
                got: types.len(),
            })
        }
    }

    pub(crate) fn get_table(&self, id: TableId) -> &dyn Table {
        &*self
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
            let index = get_index_from_tableinfo(table_info, &[col], &self.pool_set);
            match index.borrow().get_subset(&[val]) {
                Some(s) => {
                    subset.intersect(s);
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

    pub(crate) fn get_table_mut(&mut self, id: TableId) -> &mut dyn Table {
        &mut *self
            .tables
            .get_mut(id)
            .expect("must access a table that has been declared in this database")
            .table
    }

    pub(crate) fn plan_query(&mut self, query: Query, strategy: PlanStrategy) -> Plan {
        plan::plan_query(query, strategy)
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
                Rc::new(RefCell::new(Index::new(cols.to_vec(), pool_set))),
            )
        });
    if let Ok(mut ix) = index.try_borrow_mut() {
        // NB: why is try_borrow safe?
        // * We update indexes from within the execution of free join.
        // * We may use the same index more than once during a query, so
        // try_borrow_mut() can fail.
        // * But we only need to refresh the table _once_ at the beginning of
        // the query, so a single success is all we need.
        ix.refresh(table_info.table.as_ref(), pool_set);
    }
    index
}

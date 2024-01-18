//! High-level types for specifying the behavior and layout of tables.
//!
//! Tables are a mapping from some set of keys to another set of values. Tables
//! can also be "sorted by" a columna dn "partitioned by" another. This can help
//! speed up queries.

use smallvec::SmallVec;

use crate::{
    action::ExecutionState,
    common::{DenseIdMap, NumericId, Value},
    define_id,
    hash_index::PivotTable,
    offsets::{RowId, Subset},
    pool::{PoolSet, Pooled},
    row_buffer::TaggedRowBuffer,
};

define_id!(pub ColumnId, u32, "a particular column in a table");
define_id!(
    pub Generation,
    u64,
    "the current version of a table -- uesd to invalidate any existing RowIds"
);
define_id!(
    pub Offset,
    u64,
    "an opaque offset token -- used to encode iterations over a table (within a generation). These always start at 0."
);

/// The version of a table.
#[derive(Debug, PartialEq, Eq)]
pub struct TableVersion {
    /// New major generations invalidate all existing RowIds for a table.
    pub major: Generation,
    /// New minor generations within a major generation do not invalidate
    /// existing RowIds, but they may indicate that `all` can return a larger
    /// subset than before.
    pub minor: Offset,
    // NB: we may want to make `Offset` and `RowId` the same.
}

#[derive(Clone)]
pub struct TableSpec {
    /// The number of key columns for the table.
    pub n_keys: usize,

    /// The number of non-key (i.e. value) columns in the table.
    ///
    /// The total "arity" of the table is `n_keys + n_vals`.
    pub n_vals: usize,

    /// Columns that cannot be cached across generations.
    ///
    /// These columns should (e.g.) never have indexes built for them, as they
    /// will go out of date too quickly.
    pub uncacheable_columns: DenseIdMap<ColumnId, bool>,

    /// Whether or not deletions are supported for this table.
    ///
    /// Tables where this value is false are allowed to panic on calls to
    /// `stage_remove`.
    pub allows_delete: bool,
}

impl TableSpec {
    /// The total number of columns stored by the table.
    pub fn arity(&self) -> usize {
        self.n_keys + self.n_vals
    }
}

/// A constraint on the values within a row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Eq { l_col: ColumnId, r_col: ColumnId },
    EqConst { col: ColumnId, val: Value },
    LtConst { col: ColumnId, val: Value },
    GtConst { col: ColumnId, val: Value },
    LeConst { col: ColumnId, val: Value },
    GeConst { col: ColumnId, val: Value },
}

/// A row in a table.
pub struct Row {
    /// The id associated with the row.
    pub id: RowId,
    /// The Row itself.
    pub vals: Pooled<Vec<Value>>,
}

/// An interface for a table.
pub trait Table {
    /// The schema of the table.
    ///
    /// These are immutable properties of the table; callers can assume they
    /// will never change.
    fn spec(&self) -> TableSpec;

    /// Clear all table contents. If the table is nonempty, this will change the
    /// generation of the table. This method also clears any pending data.
    fn clear(&mut self);

    // Used in queries:

    /// Get a subset corresponding to all rows in the table.
    fn all(&self, pool_set: &PoolSet) -> Subset;

    /// Get the current version for the table. [`RowId`]s and [`Subset`]s are
    /// only valid for a given major generation.
    fn version(&self) -> TableVersion;

    /// Get the subset of the table that has appeared since the last offset.
    fn updates_since(&self, gen: Offset, pool_set: &PoolSet) -> Subset;

    /// Iterate over the given subset of the table, starting at an opaque
    /// `start` token, ending after up to `n` rows, returning the next start
    /// token if more rows remain. Only invoke `f` on rows that match the given
    /// constraints.
    ///
    /// This method is _not_ object safe, but it is used to define various
    /// "default" implementations of object-safe methods like `scan` and
    /// `pivot`.
    fn scan_generic_bounded(
        &self,
        subset: &Subset,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized;

    /// Group the table's contents by a set of column values.
    ///
    /// Implementors should probably use the [`default_pivot_impl`] helper for
    /// this method.
    fn pivot(&self, subset: &Subset, cols: &[ColumnId], pool_set: &PoolSet) -> PivotTable;

    /// Extract up to `n` rows from the given subset of the table starting
    /// at `start`.
    ///
    /// If any rows are available, then the next [`Offset`] to start at is
    /// returned.
    ///
    /// Implementers should probably use the [`default_scan_bounded_impl`]
    /// helper for this method.
    fn scan_bounded(
        &self,
        subset: &Subset,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset>;

    /// Extract the given columns of the rows matching the given subset of the
    /// table.
    ///
    /// Implementors should probably use the [`default_scan_project_impl`] helper for
    /// this method.
    fn scan_project(
        &self,
        subset: &Subset,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset>;

    /// Iterate over the given subset of the table.
    ///
    /// This is a variant of [`Table::scan_generic_bounded`] that iterates over
    /// the entire table.
    fn scan_generic(&self, subset: &Subset, mut f: impl FnMut(RowId, &[Value]))
    where
        Self: Sized,
    {
        let mut cur = Offset::new(0);
        while let Some(next) = self.scan_generic_bounded(subset, cur, usize::MAX, &[], |id, row| {
            f(id, row);
        }) {
            cur = next;
        }
    }

    /// Extract the rows matching the given subset of the table.
    fn scan(&self, subset: &Subset, pool: &PoolSet) -> TaggedRowBuffer {
        let arity = self.spec().arity();
        let mut buf = TaggedRowBuffer::new(arity, pool);
        assert!(self
            .scan_bounded(subset, Offset::new(0), usize::MAX, &mut buf)
            .is_none());
        buf
    }

    /// Filter a given subset of the table for the rows matching the single constraint.
    ///
    /// Implementors must provide at least one of `refine_one` or `refine`.`
    fn refine_one(&self, subset: Subset, c: &Constraint, pool_set: &PoolSet) -> Subset {
        self.refine(subset, std::slice::from_ref(c), pool_set)
    }

    /// Filter a given subset of the table for the rows matching the given constraints.
    ///
    /// Implementors must provide at least one of `refine_one` or `refine`.`
    fn refine(&self, subset: Subset, cs: &[Constraint], pool_set: &PoolSet) -> Subset {
        cs.iter()
            .fold(subset, |subset, c| self.refine_one(subset, c, pool_set))
    }

    /// An optional method for quickly generating a subset from a constraint.
    /// The standard use-case here is to apply constraints based on a column
    /// that is known to be sorted.
    ///
    /// The default implementation of `refine` evaluates these constraints first.
    fn fast_subset(&self, _: &Constraint, _: &PoolSet) -> Option<Subset> {
        None
    }

    /// A helper routine that leverages the existing `fast_subset` method to
    /// preprocess a set of constraints into "fast" and "slow" ones, returning
    /// the subet of indexes that match the fast one.
    fn split_fast_slow(
        &self,
        cs: &[Constraint],
        pool_set: &PoolSet,
    ) -> (
        Subset,                  /* the subset of the table matching all fast constraints */
        Pooled<Vec<Constraint>>, /* the fast constraints */
        Pooled<Vec<Constraint>>, /* the slow constraints */
    ) {
        let mut fast = pool_set.get::<Vec<_>>();
        let mut slow = pool_set.get::<Vec<_>>();
        let mut subset = self.all(pool_set);
        for c in cs {
            if let Some(sub) = self.fast_subset(c, pool_set) {
                subset.intersect(&sub);
                fast.push(c.clone());
            } else {
                slow.push(c.clone());
            }
        }
        (subset, fast, slow)
    }

    // Used in actions:

    /// Look up a single row by the given key values, if it is in the table.
    ///
    /// The number of values specified by `keys` should match the number of
    /// primary keys for the table.
    ///
    /// NB: we may want to vectorize this one.
    fn get_row(&self, key: &[Value], pool_set: &PoolSet) -> Option<Row>;

    /// Stage the row for insertion. Changes will not be visible until after
    /// `merge` is called.
    fn stage_insert(&mut self, row: &[Value]);

    /// Stage the keyed entries for removal. Changes will not be visible until after
    /// `merge` is called.
    fn stage_remove(&mut self, key: &[Value]);

    /// Merge any updates to the table, and potentiall update the generation for
    /// the table.
    fn merge(&mut self, exec_state: &mut ExecutionState) -> bool;
}

/// A helper for implementing the object-safe `scan_project` method in terms of `scan_generic`.
pub(crate) fn default_scan_project_impl<T: Table>(
    table: &T,
    subset: &Subset,
    cols: &[ColumnId],
    start: Offset,
    n: usize,
    cs: &[Constraint],
    out: &mut TaggedRowBuffer,
) -> Option<Offset> {
    let mut scratch = SmallVec::<[Value; 8]>::new();
    table.scan_generic_bounded(subset, start, n, cs, |id, row| {
        for col in cols {
            scratch.push(row[col.index()]);
        }
        out.add_row(id, &scratch);
        scratch.clear();
    })
}

/// A helper for implementing the object-safe `pivot` method in terms of `scan_generic`.
pub(crate) fn default_pivot_impl<T: Table>(
    table: &T,
    subset: &Subset,
    cols: &[ColumnId],
    pool_set: &PoolSet,
) -> PivotTable {
    let mut scratch = SmallVec::<[Value; 8]>::new();
    let mut res = PivotTable::new(cols.len(), pool_set);
    table.scan_generic(subset, |row_id, row| {
        for col in cols {
            scratch.push(row[col.index()]);
        }
        res.add_row(&scratch, row_id, pool_set);
        scratch.clear();
    });
    res
}

pub(crate) fn default_scan_bounded_impl<T: Table>(
    table: &T,
    subset: &Subset,
    start: Offset,
    n: usize,
    out: &mut TaggedRowBuffer,
) -> Option<Offset> {
    table.scan_generic_bounded(subset, start, n, &[], |row_id, row| {
        out.add_row(row_id, row);
    })
}

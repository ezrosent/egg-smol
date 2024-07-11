//! High-level types for specifying the behavior and layout of tables.
//!
//! Tables are a mapping from some set of keys to another set of values. Tables
//! can also be "sorted by" a columna dn "partitioned by" another. This can help
//! speed up queries.

use std::{
    any::Any,
    iter,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use numeric_id::{define_id, DenseIdMap, NumericId};
use smallvec::SmallVec;

use crate::{
    action::{
        mask::{Mask, MaskIter, ValueSource},
        Bindings, ExecutionState,
    },
    common::Value,
    hash_index::{ColumnIndex, IndexBase, TupleIndex},
    offsets::{RowId, Subset, SubsetRef},
    pool::{PoolSet, Pooled},
    row_buffer::TaggedRowBuffer,
    QueryEntry, Variable,
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
pub trait Table: Any {
    /// A variant of clone that returns a boxed trait object; this trait object
    /// must contain all of the data associated with the current table.
    fn dyn_clone(&self) -> Box<dyn Table>;

    /// A boilerplate method to make it easier to downcast values of `Table`.
    ///
    /// Implementors should be able to implement this method by returning
    /// `self`.
    fn as_any(&self) -> &dyn Any;

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

    /// Get the length of the table.
    ///
    ///
    /// This is not in general equal to the length of the `all` subset: the size
    /// of a subset is allowed to be larger than the number of table entries in
    /// range of the subset.
    fn len(&self, pool_set: &PoolSet) -> usize;

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
        subset: SubsetRef,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized;

    /// Iterate over the given subset of the table.
    ///
    /// This is a variant of [`Table::scan_generic_bounded`] that iterates over
    /// the entire table.
    fn scan_generic(&self, subset: SubsetRef, mut f: impl FnMut(RowId, &[Value]))
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
    /// These constraints are very helpful for query planning; it is a good idea
    /// to implement them.
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
                subset.intersect(sub.as_ref(), pool_set.get_pool());
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
    fn get_row(&self, key: &[Value], pool_set: &PoolSet) -> Option<Row>;

    /// Look up the given column of single row by the given key values, if it is
    /// in the table.
    ///
    /// The number of values specified by `keys` should match the number of
    /// primary keys for the table.
    fn get_row_column(&self, key: &[Value], col: ColumnId, pool_set: &PoolSet) -> Option<Value> {
        self.get_row(key, pool_set).map(|row| row.vals[col.index()])
    }

    /// Stage the row for insertion. Changes will not be visible until after
    /// `merge` is called.
    fn stage_insert(&mut self, row: &[Value]);

    /// Stage the keyed entries for removal. Changes will not be visible until after
    /// `merge` is called.
    fn stage_remove(&mut self, key: &[Value]);

    /// Merge any updates to the table, and potentially update the generation for
    /// the table.
    fn merge(&mut self, exec_state: &mut ExecutionState) -> bool;
}

struct WrapperImpl<T>(PhantomData<*const T>);

pub(crate) fn wrapper<T: Table>() -> Box<dyn TableWrapper> {
    Box::new(WrapperImpl::<T>(PhantomData))
}

impl<T: Table> TableWrapper for WrapperImpl<T> {
    fn dyn_clone(&self) -> Box<dyn TableWrapper> {
        Box::new(Self(PhantomData))
    }
    fn scan_bounded(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        table.scan_generic_bounded(subset, start, n, &[], |row_id, row| {
            out.add_row(row_id, row);
        })
    }
    fn pivot_col(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        col: ColumnId,
        pool_set: &PoolSet,
    ) -> ColumnIndex {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut res = ColumnIndex::new(pool_set);
        table.scan_generic(subset, |row_id, row| {
            res.add_row(&row[col.index()], row_id, pool_set);
        });
        res
    }
    fn pivot(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        pool_set: &PoolSet,
    ) -> TupleIndex {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut res = TupleIndex::new(cols.len(), pool_set);
        match cols {
            [] => {}
            [col] => table.scan_generic(subset, |row_id, row| {
                res.add_row(&[row[col.index()]], row_id, pool_set);
            }),
            [x, y] => table.scan_generic(subset, |row_id, row| {
                res.add_row(&[row[x.index()], row[y.index()]], row_id, pool_set);
            }),
            [x, y, z] => table.scan_generic(subset, |row_id, row| {
                res.add_row(
                    &[row[x.index()], row[y.index()], row[z.index()]],
                    row_id,
                    pool_set,
                );
            }),
            _ => {
                let mut scratch = SmallVec::<[Value; 8]>::new();
                table.scan_generic(subset, |row_id, row| {
                    for col in cols {
                        scratch.push(row[col.index()]);
                    }
                    res.add_row(&scratch, row_id, pool_set);
                    scratch.clear();
                });
            }
        }
        res
    }
    fn scan_project(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        match cols {
            [] => None,
            [col] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[col.index()]]);
            }),
            [x, y] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[x.index()], row[y.index()]]);
            }),
            [x, y, z] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[x.index()], row[y.index()], row[z.index()]]);
            }),
            _ => {
                let mut scratch = SmallVec::<[Value; 8]>::with_capacity(cols.len());
                table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                    for col in cols {
                        scratch.push(row[col.index()]);
                    }
                    out.add_row(id, &scratch);
                    scratch.clear();
                })
            }
        }
    }

    fn lookup_row_vectorized(
        &self,
        table: &dyn Table,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    ) {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut out = ps.get::<Vec<Value>>();
        match args {
            [QueryEntry::Var(v)] => {
                mask.iter(&bindings[*v])
                    .fill_vec(&mut out, Value::stale, |_, arg| {
                        table.get_row_column(&[*arg], col, ps)
                    });
            }
            [QueryEntry::Var(v1), QueryEntry::Var(v2)] => {
                mask.iter(&bindings[*v1]).zip(&bindings[*v2]).fill_vec(
                    &mut out,
                    Value::stale,
                    |_, (a1, a2)| table.get_row_column(&[*a1, *a2], col, ps),
                );
            }
            [QueryEntry::Var(v1), QueryEntry::Var(v2), QueryEntry::Var(v3)] => {
                mask.iter(&bindings[*v1])
                    .zip(&bindings[*v2])
                    .zip(&bindings[*v3])
                    .fill_vec(&mut out, Value::stale, |_, ((a1, a2), a3)| {
                        table.get_row_column(&[*a1, *a2, *a3], col, ps)
                    });
            }
            args => {
                let pool = ps.get_pool().clone();
                mask.iter_dynamic(
                    pool,
                    args.iter().map(|v| match v {
                        QueryEntry::Var(v) => ValueSource::Slice(&bindings[*v]),
                        QueryEntry::Const(c) => ValueSource::Const(*c),
                    }),
                )
                .fill_vec(&mut out, Value::stale, |_, args| {
                    table.get_row_column(&args, col, ps)
                });
            }
        };
        bindings.insert(out_var, out);
    }

    fn lookup_with_default_vectorized(
        &self,
        table: &dyn Table,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    ) {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut out = ps.get::<Vec<Value>>();
        match (args, default) {
            ([QueryEntry::Var(v)], QueryEntry::Var(default)) => mask
                .iter(&bindings[*v])
                .zip(&bindings[default])
                .fill_vec(&mut out, Value::stale, |_, (v, default)| {
                    Some(table.get_row_column(&[*v], col, ps).unwrap_or(*default))
                }),
            ([QueryEntry::Var(v1), QueryEntry::Var(v2)], QueryEntry::Var(default)) => mask
                .iter(&bindings[*v1])
                .zip(&bindings[*v2])
                .zip(&bindings[default])
                .fill_vec(&mut out, Value::stale, |_, ((a1, a2), default)| {
                    Some(
                        table
                            .get_row_column(&[*a1, *a2], col, ps)
                            .unwrap_or(*default),
                    )
                }),
            (
                [QueryEntry::Var(v1), QueryEntry::Var(v2), QueryEntry::Var(v3)],
                QueryEntry::Var(default),
            ) => mask
                .iter(&bindings[*v1])
                .zip(&bindings[*v2])
                .zip(&bindings[*v3])
                .zip(&bindings[default])
                .fill_vec(&mut out, Value::stale, |_, (((a1, a2), a3), default)| {
                    Some(
                        table
                            .get_row_column(&[*a1, *a2, *a3], col, ps)
                            .unwrap_or(*default),
                    )
                }),
            (args, default) => {
                let pool = ps.get_pool().clone();
                mask.iter_dynamic(
                    pool,
                    iter::once(&default).chain(args.iter()).map(|v| match v {
                        QueryEntry::Var(v) => ValueSource::Slice(&bindings[*v]),
                        QueryEntry::Const(c) => ValueSource::Const(*c),
                    }),
                )
                .fill_vec(&mut out, Value::stale, |_, vals| {
                    let default = vals[0];
                    let key = &vals[1..];
                    Some(table.get_row_column(key, col, ps).unwrap_or(default))
                })
            }
        };
        bindings.insert(out_var, out);
    }
}

/// A WrappedTable takes a Table and extends it with a number of helpful,
/// object-safe methods for accessing a table.
///
/// It essentially acts like an extension trait: it is a separate type to allow
/// object-safe extension methods to call methods that require `Self: Sized`.
/// The implementations here downcast manually to the type used when
/// constructing the WrappedTable.
pub struct WrappedTable {
    inner: Box<dyn Table>,
    wrapper: Box<dyn TableWrapper>,
}

impl WrappedTable {
    pub(crate) fn new<T: Table>(inner: T) -> Self {
        let wrapper = wrapper::<T>();
        let inner = Box::new(inner);
        Self { inner, wrapper }
    }

    /// Clone the contents of the table.
    pub fn dyn_clone(&self) -> Self {
        WrappedTable {
            inner: self.inner.dyn_clone(),
            wrapper: self.wrapper.dyn_clone(),
        }
    }

    /// Starting at the given [`Offset`] into `subset`, scan up to `n` rows and
    /// write them to `out`. Return the next starting offset. If no offset is
    /// returned then the subset has been scanned completely.
    pub fn scan_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        self.wrapper
            .scan_bounded(&*self.inner, subset, start, n, out)
    }

    /// Group the contents of the given subset by the given column.
    pub(crate) fn pivot_col(
        &self,
        subset: SubsetRef,
        col: ColumnId,
        pool_set: &PoolSet,
    ) -> ColumnIndex {
        self.wrapper.pivot_col(&*self.inner, subset, col, pool_set)
    }

    /// A multi-column vairant of [`WrappedTable::pivot_col`].
    pub(crate) fn pivot(
        &self,
        subset: SubsetRef,
        cols: &[ColumnId],
        pool_set: &PoolSet,
    ) -> TupleIndex {
        self.wrapper.pivot(&*self.inner, subset, cols, pool_set)
    }

    /// A variant fo [`WrappedTable::scan_bounded`] that projects a subset of
    /// columns and only appends rows that match the given constraints.
    pub fn scan_project(
        &self,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        self.wrapper
            .scan_project(&*self.inner, subset, cols, start, n, cs, out)
    }

    /// Return the contents of the subset as a [`TaggedRowBuffer`].
    pub fn scan(&self, subset: SubsetRef, pool: &PoolSet) -> TaggedRowBuffer {
        self.wrapper.scan(&*self.inner, subset, pool)
    }

    pub(crate) fn lookup_row_vectorized(
        &self,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    ) {
        self.wrapper
            .lookup_row_vectorized(&*self.inner, ps, mask, bindings, args, col, out_var);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn lookup_with_default_vectorized(
        &self,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    ) {
        self.wrapper.lookup_with_default_vectorized(
            &*self.inner,
            ps,
            mask,
            bindings,
            args,
            col,
            default,
            out_var,
        );
    }
}

impl Deref for WrappedTable {
    type Target = dyn Table;

    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl DerefMut for WrappedTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.inner
    }
}

pub(crate) trait TableWrapper {
    fn dyn_clone(&self) -> Box<dyn TableWrapper>;
    fn scan_bounded(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset>;
    fn pivot_col(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        col: ColumnId,
        pool_set: &PoolSet,
    ) -> ColumnIndex;
    fn pivot(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        pool_set: &PoolSet,
    ) -> TupleIndex;

    #[allow(clippy::too_many_arguments)]
    fn scan_project(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset>;
    fn scan(&self, table: &dyn Table, subset: SubsetRef, pool: &PoolSet) -> TaggedRowBuffer {
        let arity = table.spec().arity();
        let mut buf = TaggedRowBuffer::new(arity, pool);
        assert!(self
            .scan_bounded(table, subset, Offset::new(0), usize::MAX, &mut buf)
            .is_none());
        buf
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_row_vectorized(
        &self,
        table: &dyn Table,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    );

    #[allow(clippy::too_many_arguments)]
    fn lookup_with_default_vectorized(
        &self,
        table: &dyn Table,
        ps: &PoolSet,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    );
}

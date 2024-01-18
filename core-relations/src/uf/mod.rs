//! A table implementation backed by a union-find.

use std::{cell::RefCell, mem};

use crate::{
    action::ExecutionState,
    common::{DenseIdMap, HashMap, NumericId, Value},
    hash_index::PivotTable,
    offsets::{OffsetRange, RowId, Subset},
    pool::PoolSet,
    row_buffer::TaggedRowBuffer,
    table_spec::{
        default_pivot_impl, default_scan_bounded_impl, default_scan_project_impl, ColumnId,
        Constraint, Generation, Offset, Row, Table, TableSpec, TableVersion,
    },
};

#[cfg(test)]
mod tests;

/// A special table backed by a union-find used to efficiently implement
/// egglog-style canonicaliztion.
///
/// To canonicalize columns, we need to efficiently discover values that have
/// ceased to be canonical. To do that we keep a table of _displaced_ values:
///
/// This table has three columns:
/// 1. (the only key): a value that is _no longer canonical_ in the equivalence relation.
/// 2. The canonical value of the equivalence class.
/// 3. The timestamp at which the key stopped being canonical.
///
/// We do not store the second value explicitly: instead, we compute it
/// on-the-fly using a union-find data-structure.
///
/// This is related to the 'Leader' encoding in some versions of egglog:
/// Displaced is a version of Leader that _only_ stores ids when they cease to
/// be canonical. Rows are also "automatically updated" with the current leader,
/// rather than requiring the DB to replay history or canonicalize redundant
/// values in the table.
///
/// To union new ids `l`, and `r`, stage an update `Displaced(l, r, ts)` where
/// `ts` is the current timestamp. Note that all tie-breaks and other encoding
/// decisions are made internally, so there may not literally be a row added
/// with this value.
#[derive(Default)]
pub struct DisplacedTable {
    uf: RefCell<UnionFind>,
    displaced: Vec<(Value, Value)>,
    changed: bool,
    // staged: Vec<(Value, Value, Value)>,
    lookup_table: HashMap<Value, RowId>,
}

impl Table for DisplacedTable {
    fn spec(&self) -> TableSpec {
        let mut uncacheable_columns = DenseIdMap::default();
        // The second column of this table is determined dynamically by the union-find.
        uncacheable_columns.insert(ColumnId::new(1), true);
        TableSpec {
            n_keys: 1,
            n_vals: 2,
            uncacheable_columns,
            allows_delete: false,
        }
    }

    fn clear(&mut self) {
        self.uf.borrow_mut().reset();
        self.displaced.clear();
    }

    fn all(&self, _: &PoolSet) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::new(0),
            RowId::from_usize(self.displaced.len()),
        ))
    }

    fn version(&self) -> TableVersion {
        TableVersion {
            major: Generation::new(0),
            minor: Offset::from_usize(self.displaced.len()),
        }
    }

    fn updates_since(&self, gen: Offset, _: &PoolSet) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::from_usize(gen.index()),
            RowId::from_usize(self.displaced.len()),
        ))
    }

    fn pivot(&self, subset: &Subset, cols: &[ColumnId], pool_set: &PoolSet) -> PivotTable {
        default_pivot_impl(self, subset, cols, pool_set)
    }

    fn scan_generic_bounded(
        &self,
        subset: &Subset,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        mut f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized,
    {
        if cs.is_empty() {
            let start = start.index();
            subset
                .iter_bounded(start, start + n, |row| {
                    f(row, self.expand(row).as_slice());
                })
                .map(Offset::from_usize)
        } else {
            let start = start.index();
            subset
                .iter_bounded(start, start + n, |row| {
                    if cs.iter().all(|c| self.eval(c, row)) {
                        f(row, self.expand(row).as_slice());
                    }
                })
                .map(Offset::from_usize)
        }
    }

    fn scan_project(
        &self,
        subset: &Subset,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        default_scan_project_impl(self, subset, cols, start, n, cs, out)
    }

    fn scan_bounded(
        &self,
        subset: &Subset,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        default_scan_bounded_impl(self, subset, start, n, out)
    }

    fn refine_one(&self, mut subset: Subset, c: &Constraint, pool_set: &PoolSet) -> Subset {
        subset.retain(|row| self.eval(c, row), pool_set);
        subset
    }

    fn fast_subset(&self, constraint: &Constraint, _: &PoolSet) -> Option<Subset> {
        let ts = ColumnId::new(2);
        match constraint {
            Constraint::Eq { .. } => None,
            Constraint::EqConst { col, val } => {
                if *col == ColumnId::new(1) {
                    return None;
                }
                if *col == ColumnId::new(0) {
                    return Some(match self.lookup_table.get(val) {
                        Some(row) => Subset::Dense(OffsetRange::new(
                            *row,
                            RowId::from_usize(row.index() + 1),
                        )),
                        None => Subset::empty(),
                    });
                }
                match self.timestamp_bounds(*val) {
                    Ok((start, end)) => Some(Subset::Dense(OffsetRange::new(start, end))),
                    Err(_) => None,
                }
            }
            Constraint::LtConst { col, val } => {
                if *col != ts {
                    return None;
                }
                match self.timestamp_bounds(*val) {
                    Err(bound) | Ok((bound, _)) => {
                        Some(Subset::Dense(OffsetRange::new(RowId::new(0), bound)))
                    }
                }
            }
            Constraint::GtConst { col, val } => {
                if *col != ts {
                    return None;
                }

                match self.timestamp_bounds(*val) {
                    Err(bound) | Ok((_, bound)) => Some(Subset::Dense(OffsetRange::new(
                        bound,
                        RowId::from_usize(self.displaced.len()),
                    ))),
                }
            }
            Constraint::LeConst { col, val } => {
                if *col != ts {
                    return None;
                }

                match self.timestamp_bounds(*val) {
                    Err(bound) | Ok((_, bound)) => {
                        Some(Subset::Dense(OffsetRange::new(RowId::new(0), bound)))
                    }
                }
            }
            Constraint::GeConst { col, val } => {
                if *col != ts {
                    return None;
                }

                match self.timestamp_bounds(*val) {
                    Err(bound) | Ok((bound, _)) => Some(Subset::Dense(OffsetRange::new(
                        bound,
                        RowId::from_usize(self.displaced.len()),
                    ))),
                }
            }
        }
    }

    fn get_row(&self, key: &[Value], pool_set: &PoolSet) -> Option<Row> {
        assert_eq!(key.len(), 1, "attempt to lookup a row with the wrong key");
        let row_id = *self.lookup_table.get(&key[0])?;
        let mut vals = pool_set.get::<Vec<Value>>();
        vals.extend_from_slice(self.expand(row_id).as_slice());
        Some(Row { id: row_id, vals })
    }

    fn stage_insert(&mut self, row: &[Value]) {
        assert_eq!(row.len(), 3, "attempt to insert a row with the wrong arity");
        let mut uf = self.uf.borrow_mut();
        if uf.find(row[0]) == uf.find(row[1]) {
            return;
        }
        let (_, child) = uf.union(row[0], row[1]);
        let ts = row[2];
        if let Some((_, highest)) = self.displaced.last() {
            assert!(
                *highest <= ts,
                "must insert rows with increasing timestamps"
            );
        }
        let next = RowId::from_usize(self.displaced.len());
        self.displaced.push((child, ts));
        self.lookup_table.insert(child, next);
        self.changed = true;
    }

    fn stage_remove(&mut self, _: &[Value]) {
        panic!("attempting to delete an entry for a DisplacedTable")
    }

    fn merge(&mut self, _: &mut ExecutionState) -> bool {
        mem::take(&mut self.changed)
    }
}

impl DisplacedTable {
    fn expand(&self, row: RowId) -> [Value; 3] {
        let (child, ts) = self.displaced[row.index()];
        [child, self.uf.borrow_mut().find(child), ts]
    }
    fn timestamp_bounds(&self, val: Value) -> Result<(RowId, RowId), RowId> {
        match self.displaced.binary_search_by_key(&val, |(_, ts)| *ts) {
            Ok(mut off) => {
                let mut next = off;
                while off > 0 && self.displaced[off - 1].1 == val {
                    off -= 1;
                }
                while next < self.displaced.len() && self.displaced[next].1 == val {
                    next += 1;
                }
                Ok((RowId::from_usize(off), RowId::from_usize(next)))
            }
            Err(off) => Err(RowId::from_usize(off)),
        }
    }
    fn eval(&self, constraint: &Constraint, row: RowId) -> bool {
        let vals = self.expand(row);
        match constraint {
            Constraint::Eq { l_col, r_col } => vals[l_col.index()] == vals[r_col.index()],
            Constraint::EqConst { col, val } => vals[col.index()] == *val,
            Constraint::LtConst { col, val } => vals[col.index()] < *val,
            Constraint::GtConst { col, val } => vals[col.index()] > *val,
            Constraint::LeConst { col, val } => vals[col.index()] <= *val,
            Constraint::GeConst { col, val } => vals[col.index()] >= *val,
        }
    }
}

#[derive(Default)]
struct UnionFind {
    parents: Vec<Value>,
}

impl UnionFind {
    fn reset(&mut self) {
        for (i, v) in self.parents.iter_mut().enumerate() {
            *v = Value::new(i as u32);
        }
    }
    fn reserve(&mut self, v: Value) {
        assert!(
            !v.is_stale(),
            "attempting to insert a stale value into the union-find"
        );
        if v.index() >= self.parents.len() {
            for i in self.parents.len()..=v.index() {
                self.parents.push(Value::from_usize(i));
            }
        }
    }

    /// Merge two equivalence classes.
    pub(crate) fn union(&mut self, a: Value, b: Value) -> (Value /* parent */, Value /* child */) {
        self.reserve(a);
        self.reserve(b);
        let a = self.find(a);
        let b = self.find(b);
        if a != b {
            self.parents[a.index()] = b;
        }
        (b, a)
    }

    /// Find the representative of an equivalence class.
    pub(crate) fn find(&mut self, id: Value) -> Value {
        self.reserve(id);
        let mut cur = id;
        loop {
            let parent = self.parents[cur.index()];
            if cur == parent {
                break;
            }
            let grand = self.parents[parent.index()];
            self.parents[cur.index()] = grand;
            cur = grand;
        }
        cur
    }
}

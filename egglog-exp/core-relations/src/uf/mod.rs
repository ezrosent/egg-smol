//! A table implementation backed by a union-find.

use std::{any::Any, cell::RefCell, mem};

use indexmap::IndexMap;
use numeric_id::{DenseIdMap, NumericId};

use crate::{
    action::ExecutionState,
    common::{HashMap, IndexSet, Value},
    offsets::{OffsetRange, RowId, Subset, SubsetRef},
    pool::PoolSet,
    table_spec::{ColumnId, Constraint, Generation, Offset, Row, Table, TableSpec, TableVersion},
};

#[cfg(test)]
mod tests;

type UnionFind = union_find::UnionFind<Value>;

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
    lookup_table: HashMap<Value, RowId>,
}

impl Clone for DisplacedTable {
    fn clone(&self) -> Self {
        let uf = self.uf.borrow().clone();
        DisplacedTable {
            uf: RefCell::new(uf),
            displaced: self.displaced.clone(),
            changed: self.changed,
            lookup_table: self.lookup_table.clone(),
        }
    }
}

impl Table for DisplacedTable {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
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

    fn len(&self, _: &PoolSet) -> usize {
        self.displaced.len()
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

    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
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

    fn get_row_column(&self, key: &[Value], col: ColumnId, _: &PoolSet) -> Option<Value> {
        assert_eq!(key.len(), 1, "attempt to lookup a row with the wrong key");
        let row_id = *self.lookup_table.get(&key[0])?;
        Some(self.expand(row_id)[col.index()])
    }

    fn stage_insert(&mut self, row: &[Value]) {
        self.changed |= self.insert_impl(row).is_some();
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
        eval_constraint(&vals, constraint)
    }
    fn insert_impl(&mut self, row: &[Value]) -> Option<(Value, Value)> {
        assert_eq!(row.len(), 3, "attempt to insert a row with the wrong arity");
        let mut uf = self.uf.borrow_mut();
        if uf.find(row[0]) == uf.find(row[1]) {
            return None;
        }
        let (parent, child) = uf.union(row[0], row[1]);
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
        Some((parent, child))
    }
}

/// A variant of `DisplacedTable` that also stores "provenance" information that
/// can be used to generate proofs of equality. This table expects a fourth
/// "proof" column, though the values it hands back _are not_ the proofs that
/// come in and generally should not be used directly.
///
/// To generate a proof that two values are equal, this table exports a separate
/// `get_proof` method.
#[derive(Clone, Default)]
pub struct DisplacedTableWithProvenance {
    base: DisplacedTable,
    /// Added context for a given "displaced" row. We use this to store "proofs
    /// that x = y".
    ///
    /// N.B. We currently only use the first proof that we find. The remaining
    /// proofs are used for debugging, and hopefully eventually also to generate
    /// smaller proofs.
    context: HashMap<(Value, Value), IndexSet<Value>>,
    /// The value that was displaced, the value _immediately_ displacing it.
    displaced: Vec<(Value, Value)>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ProofStep {
    Forward(Value),
    Backward(Value),
}

impl DisplacedTableWithProvenance {
    fn expand(&self, row: RowId) -> [Value; 4] {
        let [v1, v2, v3] = self.base.expand(row);
        let (child, parent) = self.displaced[row.index()];
        debug_assert_eq!(child, v1);
        let proof = *self.context[&(child, parent)].get_index(0).unwrap();
        [v1, v2, v3, proof]
    }

    fn eval(&self, constraint: &Constraint, row: RowId) -> bool {
        eval_constraint(&self.expand(row), constraint)
    }

    /// A simple proof generation algorithm, based on "Proof-Producing
    /// Congruence Closure" by Nieuwenhuis and Oliveras. If the two values are
    /// not equal, this method returns `None`.
    ///
    /// We want to make this a lot more sophisticated eventually; this is a
    /// simple implementation that can produce very long proofs.
    pub fn get_proof(&self, l: Value, r: Value) -> Option<Vec<ProofStep>> {
        if l == r {
            return Some(vec![]);
        }
        let mut l_proofs = IndexMap::new();
        let mut r_proofs = IndexMap::new();
        let mut uf = self.base.uf.borrow_mut();
        let canon = uf.find(l);
        if uf.find(r) != canon {
            // The two values aren't equal.
            return None;
        }

        // General case: collect individual equality proofs that point from `l`
        // (sim. `r`) and move towards canon. We stop early and don't always go
        // to `canon`. To see why consider the following sequences of unions.
        // For simplicity, we'll assume that the "leader" (or new canonical id)
        // is always the second argument to `union`.
        // * left:  A: union(0,2), B: union(2,4), C: union(4,6)
        // * right: D: union(1,3), E: union(3,5), F: union(5,4), C: union(4,6)
        // Where `l` `r` are 0 and 1, and their canonical value is `6`.
        // A simple approach here would be to simply glue the proofs that `l=6`
        // and `r=6` together, something like:
        //
        //    [A;B;C;rev(C);rev(F);rev(E);rev(D)]
        //
        // The code below avoids the redundant common suffix (i.e. `C;rev(C)`)
        // and just uses A,B,D,E, and F.
        //
        // In addition to allowing us to generate smaller proofs, this sort of
        // algorithm also ensures that we are returning the first proof of `l =
        // r` that we learned about, which is important for avoiding cycles when
        // reconstructing a proof.

        // General case: create a proof  that l = canon, then compose it with
        // the proof that r = canon, reversed.
        for (mut cur, steps) in [(l, &mut l_proofs), (r, &mut r_proofs)] {
            while cur != canon {
                // Find where cur became non-canonical.
                let row = *self.base.lookup_table.get(&cur).unwrap();
                let (child, parent) = self.displaced[row.index()];
                let proof = *self.context[&(child, parent)].get_index(0).unwrap();
                steps.insert(parent, proof);
                cur = parent;
            }
        }

        let mut l_end = None;
        let mut r_start = None;

        if let Some(i) = r_proofs.get_index_of(&l) {
            r_start = Some(i);
        } else {
            for (i, (next_id, _)) in l_proofs.iter().enumerate() {
                if *next_id == r {
                    l_end = Some(i);
                    break;
                }
                if let Some(j) = r_proofs.get_index_of(next_id) {
                    l_end = Some(i);
                    r_start = Some(j);
                    break;
                }
            }
        }
        match (l_end, r_start) {
            (None, Some(start)) => Some(
                r_proofs.as_slice()[..=start]
                    .iter()
                    .rev()
                    .map(|(_, proof)| ProofStep::Backward(*proof))
                    .collect(),
            ),
            (Some(end), None) => Some(
                l_proofs.as_slice()[..=end]
                    .iter()
                    .map(|(_, proof)| ProofStep::Forward(*proof))
                    .collect(),
            ),
            (Some(end), Some(start)) => Some(
                l_proofs.as_slice()[..=end]
                    .iter()
                    .map(|(_, proof)| ProofStep::Forward(*proof))
                    .chain(
                        r_proofs.as_slice()[..=start]
                            .iter()
                            .rev()
                            .map(|(_, proof)| ProofStep::Backward(*proof)),
                    )
                    .collect(),
            ),
            (None, None) => {
                panic!("did not find common id, despite the values being equivalent {l:?} / {r:?}, l_proofs={l_proofs:?}, r_proofs={r_proofs:?}")
            }
        }
    }
}

impl Table for DisplacedTableWithProvenance {
    fn refine_one(&self, mut subset: Subset, c: &Constraint, pool_set: &PoolSet) -> Subset {
        subset.retain(|row| self.eval(c, row), pool_set);
        subset
    }
    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
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

    fn spec(&self) -> TableSpec {
        TableSpec {
            n_vals: 3,
            ..self.base.spec()
        }
    }
    fn stage_insert(&mut self, row: &[Value]) {
        let [a, b, c, d] = row else {
            panic!("invalid arity for row: {row:?} (expected 4)")
        };
        match self.base.insert_impl(&[*a, *b, *c]) {
            Some((parent, child)) => {
                // NB: parent and child may not be `a` or `b`. We are currently
                // treaing `d` as though it just _is_ a proof the `a` equals `b`,
                // but we may need some way of tacking on a proof that `a`
                // equals parent, etc.
                self.displaced.push((child, parent));
                self.context.entry((child, parent)).or_default().insert(*d);
                self.base.changed = true;
            }
            None => {
                self.context.entry((*a, *b)).or_default().insert(*d);
                // We don't register a change, even if we learned a new proof.
                // We may want to change this behavior in order to search for
                // smaller proofs.
            }
        }
    }

    fn merge(&mut self, exec_state: &mut ExecutionState) -> bool {
        self.base.merge(exec_state)
    }

    fn get_row(&self, key: &[Value], pool_set: &PoolSet) -> Option<Row> {
        let mut inner = self.base.get_row(key, pool_set)?;
        let (child, parent) = self.displaced[inner.id.index()];
        debug_assert_eq!(child, inner.vals[0]);
        let proof = *self.context[&(child, parent)].get_index(0).unwrap();
        inner.vals.push(proof);
        Some(inner)
    }

    fn get_row_column(&self, key: &[Value], col: ColumnId, pool_set: &PoolSet) -> Option<Value> {
        if col == ColumnId::new(3) {
            let row = *self.base.lookup_table.get(&key[0])?;
            Some(self.expand(row)[3])
        } else {
            self.base.get_row_column(key, col, pool_set)
        }
    }

    // Many of these methods just delgate to `base`:

    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn clear(&mut self) {
        self.base.clear()
    }
    fn all(&self, pool_set: &PoolSet) -> Subset {
        self.base.all(pool_set)
    }
    fn len(&self, pool_set: &PoolSet) -> usize {
        self.base.len(pool_set)
    }
    fn updates_since(&self, gen: Offset, pool_set: &PoolSet) -> Subset {
        self.base.updates_since(gen, pool_set)
    }
    fn version(&self) -> TableVersion {
        self.base.version()
    }
    fn fast_subset(&self, c: &Constraint, ps: &PoolSet) -> Option<Subset> {
        self.base.fast_subset(c, ps)
    }
    fn stage_remove(&mut self, key: &[Value]) {
        self.base.stage_remove(key)
    }
}

fn eval_constraint<const N: usize>(vals: &[Value; N], constraint: &Constraint) -> bool {
    match constraint {
        Constraint::Eq { l_col, r_col } => vals[l_col.index()] == vals[r_col.index()],
        Constraint::EqConst { col, val } => vals[col.index()] == *val,
        Constraint::LtConst { col, val } => vals[col.index()] < *val,
        Constraint::GtConst { col, val } => vals[col.index()] > *val,
        Constraint::LeConst { col, val } => vals[col.index()] <= *val,
        Constraint::GeConst { col, val } => vals[col.index()] >= *val,
    }
}

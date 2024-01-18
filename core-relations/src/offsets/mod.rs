use std::{cmp, fmt, mem};

use crate::{
    common::NumericId,
    define_id,
    pool::{Clear, PoolSet, Pooled},
};

define_id!(pub RowId, u32, "a numeric offset into a table");

#[cfg(test)]
mod tests;

/// A trait for types that represent a sequence of sorted offsets into a table.
///
/// NB: this trait may have outlived its usefulness. We may want to just get rid
/// of it.
pub(crate) trait Offsets {
    // A half-open range enclosing the offsets in this sequence.
    fn bounds(&self) -> Option<(RowId, RowId)>;
    fn is_empty(&self) -> bool {
        self.bounds().map_or(true, |(lo, hi)| lo == hi)
    }
    fn offsets(&self, f: impl FnMut(RowId));
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub struct OffsetRange {
    start: RowId,
    end: RowId,
}

impl Offsets for OffsetRange {
    fn bounds(&self) -> Option<(RowId, RowId)> {
        Some((self.start, self.end))
    }

    fn offsets(&self, f: impl FnMut(RowId)) {
        RowId::range(self.start, self.end).for_each(f)
    }
}

impl OffsetRange {
    pub(crate) fn new(start: RowId, end: RowId) -> OffsetRange {
        assert!(
            start <= end,
            "attempting to create malformed range {start:?}..{end:?}"
        );
        OffsetRange { start, end }
    }
    pub(crate) fn size(&self) -> usize {
        self.end.index() - self.start.index()
    }
}

#[derive(Default, Clone, PartialEq, Eq, Debug)]
pub struct SortedOffsetVector(Vec<RowId>);

impl SortedOffsetVector {
    pub(crate) fn slice(&self) -> &SortedOffsetSlice {
        // SAFETY: self.0 is sorted.
        unsafe { SortedOffsetSlice::new_unchecked(&self.0) }
    }

    pub(crate) fn push(&mut self, offset: RowId) {
        assert!(self.0.last().map_or(true, |last| last <= &offset));
        // SAFETY: we just checked the invariant
        unsafe { self.push_unchecked(offset) }
    }

    pub(crate) unsafe fn push_unchecked(&mut self, offset: RowId) {
        self.0.push(offset)
    }

    pub(crate) fn retain(&mut self, mut f: impl FnMut(RowId) -> bool) {
        self.0.retain(|off| f(*off))
    }

    pub(crate) fn extend_nonoverlapping(&mut self, other: &SortedOffsetSlice) {
        if other.inner().is_empty() {
            return;
        }
        if self.0.is_empty() {
            self.0.extend(other.iter());
            return;
        }
        if self.0.last().unwrap() <= other.inner().first().unwrap() {
            self.0.extend(other.iter());
            return;
        }
        panic!("attempting to extend with overlapping offsets")
    }

    /// Overwrite the contents of the current vector with those of the offset range.
    pub(crate) fn fill_from_dense(&mut self, range: &OffsetRange) {
        self.0.clear();
        self.0
            .extend((range.start.index()..range.end.index()).map(|x| RowId::new(x as _)));
    }
}

impl Clear for SortedOffsetVector {
    fn clear(&mut self) {
        self.0.clear()
    }
    fn reuse(&self) -> bool {
        self.0.capacity() > 0
    }
}

impl Offsets for SortedOffsetVector {
    fn bounds(&self) -> Option<(RowId, RowId)> {
        self.slice().bounds()
    }

    fn offsets(&self, f: impl FnMut(RowId)) {
        self.slice().offsets(f)
    }
}

#[derive(PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct SortedOffsetSlice([RowId]);

impl fmt::Debug for SortedOffsetSlice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl SortedOffsetSlice {
    unsafe fn new_unchecked(slice: &[RowId]) -> &SortedOffsetSlice {
        debug_assert!(slice.windows(2).all(|w| w[0] <= w[1]));
        // SAFETY: SortedOffsetSlice is repr(transparent), so the two layouts are compatible.
        mem::transmute::<&[RowId], &SortedOffsetSlice>(slice)
    }
    fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = RowId> + '_ {
        self.0.iter().copied()
    }

    pub(crate) fn inner(&self) -> &[RowId] {
        &self.0
    }

    pub(crate) fn subslice(&self, lo: usize, hi: usize) -> &SortedOffsetSlice {
        // Safety: any subslice of a sorted slice is sorted.
        unsafe { SortedOffsetSlice::new_unchecked(&self.inner()[lo..hi]) }
    }

    /// Return the index of the first offset in the slice that is greater than or equal to `target`.
    pub(crate) fn binary_search_by_id(&self, target: RowId) -> usize {
        match self.inner().binary_search(&target) {
            Ok(mut found) => {
                // This is O(n), but offset slices probably won't have duplicates at all.
                while found > 0 && self.inner()[found - 1] == target {
                    found -= 1;
                }
                found
            }
            Err(x) => x,
        }
    }

    fn scan_for_offset(&self, start: usize, target: RowId) -> Result<usize, usize> {
        let mut i = start;
        while i + 1 < self.len() && self.inner()[i] < target {
            i += 1;
        }
        if i < self.len() && self.inner()[i] == target {
            Ok(i)
        } else {
            Err(i)
        }
    }
}

impl Offsets for SortedOffsetSlice {
    fn bounds(&self) -> Option<(RowId, RowId)> {
        Some((
            *self.0.first()?,
            RowId::from_usize(self.0.last()?.index() + 1),
        ))
    }

    fn offsets(&self, f: impl FnMut(RowId)) {
        self.0.iter().copied().for_each(f)
    }
}

impl<'a> Offsets for &'a SortedOffsetSlice {
    fn bounds(&self) -> Option<(RowId, RowId)> {
        Some((
            *self.0.first()?,
            RowId::from_usize(self.0.last()?.index() + 1),
        ))
    }

    fn offsets(&self, f: impl FnMut(RowId)) {
        self.0.iter().copied().for_each(f)
    }
}

/// Either or an offset range or a sorted offset vector.
#[derive(Debug)]
pub enum Subset {
    Dense(OffsetRange),
    Sparse(Pooled<SortedOffsetVector>),
}

impl Offsets for Subset {
    fn bounds(&self) -> Option<(RowId, RowId)> {
        match self {
            Subset::Dense(r) => r.bounds(),
            Subset::Sparse(s) => s.slice().bounds(),
        }
    }
    fn offsets(&self, f: impl FnMut(RowId)) {
        match self {
            Subset::Dense(r) => r.offsets(f),
            Subset::Sparse(s) => s.slice().offsets(f),
        }
    }
}

impl Clone for Subset {
    fn clone(&self) -> Self {
        match self {
            Subset::Dense(r) => Subset::Dense(*r),
            Subset::Sparse(s) => Subset::Sparse(Pooled::cloned(s)),
        }
    }
}

// TODO: consider making Subset::Sparse an Rc, so copies are shallow?

impl Subset {
    pub(crate) fn size(&self) -> usize {
        match self {
            Subset::Dense(range) => range.size(),
            Subset::Sparse(vec) => vec.0.len(),
        }
    }

    pub(crate) fn iter_bounded(
        &self,
        start: usize,
        end: usize,
        mut f: impl FnMut(RowId),
    ) -> Option<usize> {
        match self {
            Subset::Dense(r) => {
                let mut cur = start;
                for row in (r.start.index() + start.index())
                    ..cmp::min(r.start.index().saturating_add(end), r.end.index())
                {
                    f(RowId::new(row as _));
                    cur += 1;
                }
                if cur + r.start.index() < r.end.index() {
                    Some(cur)
                } else {
                    None
                }
            }
            Subset::Sparse(vec) => {
                let end = cmp::min(vec.0.len(), end);
                let next = if end == vec.0.len() { None } else { Some(end) };
                vec.0[start..end].iter().copied().for_each(f);
                next
            }
        }
    }
    pub(crate) fn retain(&mut self, mut filter: impl FnMut(RowId) -> bool, pool_set: &PoolSet) {
        match self {
            Subset::Dense(offs) => {
                let mut res = Subset::empty();
                offs.offsets(|row| {
                    if filter(row) {
                        res.add_row_sorted(row, pool_set);
                    }
                });
                *self = res;
            }
            Subset::Sparse(offs) => offs.retain(filter),
        }
    }
    /// Remove any elements of the current subset not present in `other`.
    pub(crate) fn intersect(&mut self, other: &Subset) {
        match (self, other) {
            (Subset::Dense(cur), Subset::Dense(other)) => {
                let resl = cmp::max(cur.start, other.start);
                let resr = cmp::min(cur.end, other.end);
                if resl >= resr {
                    *cur = OffsetRange::new(resl, resl);
                } else {
                    *cur = OffsetRange::new(resl, resr);
                }
            }
            (x @ Subset::Dense(_), Subset::Sparse(sparse)) => {
                let (low, hi) = x.bounds().unwrap();
                if sparse.bounds().is_some() {
                    let mut res = Pooled::new(sparse);
                    let l = sparse.slice().binary_search_by_id(low);
                    let r = sparse.slice().binary_search_by_id(hi);
                    let subslice = sparse.slice().subslice(l, r);
                    res.extend_nonoverlapping(subslice);
                    *x = Subset::Sparse(res);
                } else {
                    // empty range
                    *x = Subset::Dense(OffsetRange::new(RowId::new(0), RowId::new(0)));
                }
            }
            (Subset::Sparse(sparse), Subset::Dense(dense)) => {
                let r = sparse.slice().binary_search_by_id(dense.end);
                sparse.0.truncate(r);
                sparse.retain(|row| row >= dense.start);
            }
            (Subset::Sparse(cur), Subset::Sparse(other)) => {
                // O(n) merge operation, customized to 'retain'.
                let mut other_off = 0;
                cur.retain(
                    |rowid| match other.slice().scan_for_offset(other_off, rowid) {
                        Ok(found) => {
                            other_off = found + 1;
                            true
                        }
                        Err(next_off) => {
                            other_off = next_off;
                            false
                        }
                    },
                )
            }
        }
    }

    /// Append the given row id to the Subset.
    ///
    /// # Panics
    /// The row id in question must be greater than or equal to the upper bound
    /// of the subset. This method will panic if it is not.
    pub(crate) fn add_row_sorted(&mut self, row: RowId, pool_set: &PoolSet) {
        match self {
            Subset::Dense(range) => {
                if range.end == range.start {
                    range.start = row;
                    range.end = RowId::from_usize(row.index() + 1);
                    return;
                }
                if range.end == row {
                    range.end = RowId::from_usize(range.end.index() + 1);
                    return;
                }
                let mut vec = pool_set.get::<SortedOffsetVector>();
                vec.fill_from_dense(range);
                vec.push(row);
                *self = Subset::Sparse(vec);
            }
            Subset::Sparse(s) => {
                s.push(row);
            }
        }
    }

    pub(crate) fn empty() -> Subset {
        Subset::Dense(OffsetRange::new(RowId::new(0), RowId::new(0)))
    }
}

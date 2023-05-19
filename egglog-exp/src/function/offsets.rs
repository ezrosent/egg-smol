use std::{cmp, fmt, mem};

use crate::{common::NumericId, define_id, pool::Clear};

use super::{table::Table, Value};

define_id!(pub(crate) Offset, u32, "a numeric offset into a table");

/// A trait for types that represent a sequence of sorted offsets into a table.
pub(crate) trait Offsets {
    // A half-open range enclosing the offsets in this sequence.
    fn bounds(&self) -> Option<(Offset, Offset)>;
    fn offsets(&self, f: impl FnMut(Offset));
    fn iter_table(&self, table: &Table, mut f: impl FnMut(Offset, &[Value], Value)) {
        let Some((_, high)) =  self.bounds() else {
            // No offsets.
            return;
        };
        assert!(high.index() <= table.offset_limit().index());
        self.offsets(|o| {
            // SAFETY: all offsets are in bounds.
            let (k, v) = unsafe { table.get_offset_unchecked(o) };
            if v.is_stale() {
                return;
            }
            f(o, k, v);
        });
    }
    fn filter_table(
        &self,
        table: &Table,
        mut f: impl FnMut(&[Value], Value) -> bool,
        res: &mut SortedOffsetVector,
    ) {
        if res.0.is_empty() {
            self.iter_table(table, |o, k, v| {
                if f(k, v) {
                    // SAFETY: `self` is sorted.
                    unsafe {
                        res.push_unchecked(o);
                    }
                }
            });
        } else {
            self.iter_table(table, |o, k, v| {
                if f(k, v) {
                    res.push(o);
                }
            });
        }
    }
    fn iter_slice<T>(&self, items: &[T], mut f: impl FnMut(&T)) {
        self.iter_offset_slice(items, |_, t| f(t))
    }
    fn iter_offset_slice<T>(&self, items: &[T], mut f: impl FnMut(Offset, &T)) {
        let Some((_, high)) =  self.bounds() else {
            // No offsets.
            return;
        };
        assert!(high.index() <= items.len());
        self.offsets(|o| {
            // SAFETY: all offsets are in bounds.
            unsafe {
                f(o, items.get_unchecked(o.index()));
            }
        });
    }
    fn filter<T>(&self, items: &[T], mut f: impl FnMut(&T) -> bool, res: &mut SortedOffsetVector) {
        if res.0.is_empty() {
            self.iter_offset_slice(items, |o, t| {
                if f(t) {
                    // SAFETY: `self` is sorted.
                    unsafe {
                        res.push_unchecked(o);
                    }
                }
            });
        } else {
            self.iter_offset_slice(items, |o, t| {
                if f(t) {
                    res.push(o);
                }
            });
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct OffsetRange {
    start: Offset,
    end: Offset,
}

impl Offsets for OffsetRange {
    fn bounds(&self) -> Option<(Offset, Offset)> {
        Some((self.start, self.end))
    }

    fn offsets(&self, f: impl FnMut(Offset)) {
        Offset::range(self.start, self.end).for_each(f)
    }
}

impl OffsetRange {
    pub(crate) fn new(start: Offset, end: Offset) -> OffsetRange {
        assert!(start <= end);
        OffsetRange { start, end }
    }
    pub(crate) fn chunks(&self, chunk_size: usize) -> impl Iterator<Item = OffsetRange> {
        fn get_chunk(start: u32, end: u32, chunk: u32, chunk_size: u32) -> OffsetRange {
            OffsetRange {
                start: Offset::new(start + (chunk * chunk_size)),
                end: Offset::new(cmp::min(start + (chunk + 1) * chunk_size, end)),
            }
        }
        assert!(chunk_size <= u32::MAX as usize);
        let start = self.start.index() as u32;
        let end = self.end.index() as u32;
        (0u32..)
            .map(move |x| get_chunk(start, end, x, chunk_size as u32))
            .take_while(move |x| x.start < Offset::new(end))
    }
    pub(crate) fn size(&self) -> usize {
        self.end.index() - self.start.index()
    }
}

#[derive(Default, Clone, PartialEq, Eq, Debug)]
pub(crate) struct SortedOffsetVector(Vec<Offset>);

impl SortedOffsetVector {
    #[cfg(test)]
    pub(crate) fn new(mut offsets: Vec<Offset>) -> SortedOffsetVector {
        offsets.sort();
        SortedOffsetVector(offsets)
    }

    pub(crate) fn slice(&self) -> &SortedOffsetSlice {
        // SAFETY: self.0 is sorted.
        unsafe { SortedOffsetSlice::new_unchecked(&self.0) }
    }

    pub(crate) fn push(&mut self, offset: Offset) {
        assert!(self.0.last().map_or(true, |last| last <= &offset));
        // SAFETY: we just checked the invariant
        unsafe { self.push_unchecked(offset) }
    }

    pub(crate) unsafe fn push_unchecked(&mut self, offset: Offset) {
        self.0.push(offset)
    }

    pub(crate) fn retain(&mut self, mut f: impl FnMut(Offset) -> bool) {
        self.0.retain(|off| f(*off))
    }
}

impl Clear for SortedOffsetVector {
    type Factory = ();
    type Args<'a> = ();
    fn new(_: &()) -> Self {
        Self::default()
    }
    fn clear(&mut self) {
        self.0.clear()
    }
}

impl Offsets for SortedOffsetVector {
    fn bounds(&self) -> Option<(Offset, Offset)> {
        self.slice().bounds()
    }

    fn offsets(&self, f: impl FnMut(Offset)) {
        self.slice().offsets(f)
    }
}

#[derive(PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct SortedOffsetSlice([Offset]);

impl fmt::Debug for SortedOffsetSlice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl SortedOffsetSlice {
    unsafe fn new_unchecked(slice: &[Offset]) -> &SortedOffsetSlice {
        debug_assert!(slice.windows(2).all(|w| w[0] <= w[1]));
        // SAFETY: SortedOffsetSlice is repr(transparent), so the two layouts are compatible.
        mem::transmute::<&[Offset], &SortedOffsetSlice>(slice)
    }
    fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Offset> + '_ {
        self.0.iter().copied()
    }
    pub(crate) fn chunks(&self, chunk_size: usize) -> impl Iterator<Item = &SortedOffsetSlice> {
        self.0.chunks(chunk_size).map(|x| {
            // SAFETY: self.0 is sorted, so each chunk is sorted.
            unsafe { SortedOffsetSlice::new_unchecked(x) }
        })
    }
}

impl Offsets for SortedOffsetSlice {
    fn bounds(&self) -> Option<(Offset, Offset)> {
        Some((
            *self.0.first()?,
            Offset::from_usize(self.0.last()?.index() + 1),
        ))
    }

    fn offsets(&self, f: impl FnMut(Offset)) {
        self.0.iter().copied().for_each(f)
    }
}

impl<'a> Offsets for &'a SortedOffsetSlice {
    fn bounds(&self) -> Option<(Offset, Offset)> {
        Some((
            *self.0.first()?,
            Offset::from_usize(self.0.last()?.index() + 1),
        ))
    }

    fn offsets(&self, f: impl FnMut(Offset)) {
        self.0.iter().copied().for_each(f)
    }
}

/// `RangeOrSlice` represents either an [`OffsetRange`] or a slice of offsets.
/// We keep the type parameter `T` abstract because we will use frames to
/// dynamically adjust the lifetime of the slices it manages.
#[derive(PartialEq, Eq, Debug, Clone)]
#[repr(C)]
pub(crate) enum RangeOrSlice<T> {
    Range(OffsetRange),
    Slice(T),
}

impl<T: Offsets> Offsets for RangeOrSlice<T> {
    fn bounds(&self) -> Option<(Offset, Offset)> {
        match self {
            RangeOrSlice::Range(r) => r.bounds(),
            RangeOrSlice::Slice(s) => s.bounds(),
        }
    }
    fn offsets(&self, f: impl FnMut(Offset)) {
        match self {
            RangeOrSlice::Range(r) => r.offsets(f),
            RangeOrSlice::Slice(s) => s.offsets(f),
        }
    }
}

impl<'a> RangeOrSlice<&'a SortedOffsetSlice> {
    /// The number of offsets in this RangeOrSlice.
    pub(crate) fn size(&self) -> usize {
        match self {
            RangeOrSlice::Range(r) => r.size(),
            RangeOrSlice::Slice(s) => s.len(),
        }
    }

    pub(crate) fn chunks(
        &self,
        chunk_size: usize,
    ) -> impl Iterator<Item = RangeOrSlice<&'a SortedOffsetSlice>> {
        match self {
            RangeOrSlice::Range(r) => EitherIter::L(r.chunks(chunk_size)),
            RangeOrSlice::Slice(s) => EitherIter::R(s.chunks(chunk_size)),
        }
    }

    pub(crate) fn is_slice(&self) -> bool {
        matches!(self, RangeOrSlice::Slice(_))
    }
}

enum EitherIter<L, R> {
    L(L),
    R(R),
}

impl<'a, L: Iterator<Item = OffsetRange>, R: Iterator<Item = &'a SortedOffsetSlice>> Iterator
    for EitherIter<L, R>
{
    type Item = RangeOrSlice<&'a SortedOffsetSlice>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            EitherIter::L(l) => l.next().map(RangeOrSlice::Range),
            EitherIter::R(r) => r.next().map(RangeOrSlice::Slice),
        }
    }
}

//! A utility for managing an array of objects with varying lifetimes.
//!
use std::{
    cell::RefCell,
    fmt::{self, Debug},
    marker::PhantomData,
    mem, ops,
};

use crate::{
    common::NumericId,
    free_join::AtomId,
    function::{
        index::Index,
        index_cache::IndexCacheResult,
        offsets::{RangeOrSlice, SortedOffsetSlice},
    },
    pool::{Pool, PoolRef},
};

#[cfg(test)]
mod tests;

/// An OffsetFrame provides a scoped handle to a mutable array of
/// [`RangeOrSlice`] values.
///
/// OffsetRange has three lifetime parameters:
///
/// * `'parent` is used to track the fact that a frame holds a mutable borrow
///    for its parent frame.
/// * `'a` is used to track the lifetimes handed out by the current frame. This
///    is an explicit lifetime because it must be invariant.
/// * `'pool` is the lifetime of the pool used to allocate the vector of values
///    overwritten in this frame.
///
/// OffsetFramse can be narrowed to support storing elements that live for less
/// time than the data originally used to initialize the frame. Rust's borrowing
/// rules ensure that such values are only accessible from scopes in which the
/// references are valid.
///
/// # Safety
///
/// To narrow frames safely, use the callback-based API in
/// [`OffsetFrame::with_narrowed`]. This is a more restrictive version of the
/// API for [`OffsetFrame::narrow`]. The latter method is safe so long as all
/// child `OffsetFrame`s are dropped before the parents are used again.
pub(crate) struct OffsetFrame<'pool, 'parent, 'a> {
    /// Invariant: 'parent: 'a
    /// Invariant: data is valid for 'parent and its contents are valid for
    /// 'a (but perhaps not 'parent).
    data: *mut [Slot<'pool, *const SortedOffsetSlice>],
    to_replace: PoolRef<'pool, Vec<(usize, Slot<'pool, *const SortedOffsetSlice>)>>,
    _marker: PhantomData<(&'parent mut (), &'a mut ())>,
}

/// A slot in an OffsetFrame. Slots contain the current viable offsets for a
/// given Atom. Slots also cache any index generated for the set of offsets.
///
/// Caching indices in this way only works because of how the free join
/// algorithm is implemented: a given set of offsets in a frame will only be
/// instantiated with (at most) a single set of arguments before being replaced
/// with a refined set of offsets. In general, the offsets associated with an
/// atom are not sufficient to determine the index to build for those offsets.
#[derive(Debug)]
#[repr(C)]
pub(crate) struct Slot<'pool, T> {
    offsets: RangeOrSlice<T>,
    // Why RefCell and not just &mut ? We do not want to be able to hand out any
    // &mut Slots: Slots can only be replaced, not modified in an unrestricted
    // way. However, we still want to be able to cache `index` values, RefCell
    // lets us allow mutations to this variable alone.
    //
    // There is probably a cleaner way to do this using Pin, but this code is
    // gnarly enough already.
    index: RefCell<Option<IndexCacheResult<'pool, Index<'pool>>>>,
}

impl<'pool, T> Slot<'pool, T> {
    pub(crate) fn new(offsets: RangeOrSlice<T>) -> Self {
        Self {
            offsets,
            index: RefCell::new(None),
        }
    }

    /// Get the current offsets associated with this slot.
    pub(crate) fn offsets(&self) -> &RangeOrSlice<T> {
        &self.offsets
    }

    /// Get the index associated with this slot, generating and caching one if
    /// necessary.
    pub(crate) fn get_index(
        &self,
        generate: impl FnOnce() -> IndexCacheResult<'pool, Index<'pool>>,
    ) -> IndexCacheResult<'pool, Index<'pool>> {
        self.index.borrow_mut().get_or_insert_with(generate).clone()
    }
}

impl<'pool, 'a, 'b> OffsetFrame<'pool, 'a, 'b> {
    /// Initialize an OffsetFrame with the given initial values.
    pub(crate) fn new(
        data: &'a mut [Slot<'pool, &'b SortedOffsetSlice>],
        pool: &'pool Pool<Vec<(usize, Slot<'pool, *const SortedOffsetSlice>)>>,
    ) -> Self {
        Self {
            data: data as *mut _ as *mut _,
            to_replace: pool.get_default(),
            _marker: PhantomData,
        }
    }
}

impl<'pool, 'parent, 'a> Debug for OffsetFrame<'pool, 'parent, 'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let items: Vec<_> = self.iter().collect();
        f.debug_map().entries(items).finish()
    }
}

impl<'pool, 'parent, 'a> OffsetFrame<'pool, 'parent, 'a> {
    /// Return a frame for a smaller scope than the current one.
    ///
    /// The `&'child mut self` requirement ensures that you cannot call 'get' on
    /// this frame for as long as the child is valid.
    ///
    /// # Safety
    /// This function is safe to call so long as the returned OffsetFrame is
    /// always dropped. The drop method for `OffsetFrame` ensures that no values
    /// local to the current frame can leak back to the parent, where pointers
    /// may be dangling.
    ///
    /// For a safe variant, see the CPS'd version [`OffsetFrame::with_narrowed`].
    unsafe fn narrow<'child>(&'child mut self) -> OffsetFrame<'pool, 'a, 'child>
    where
        'a: 'child,
    {
        // * We enforce that 'parent: 'a here in the lifetime bound.
        // * Because lifetimes only get shorter, the contents of `data` remain
        //   valid.
        OffsetFrame {
            data: self.data,
            to_replace: self.to_replace.pool().get_default(),
            _marker: PhantomData,
        }
    }

    /// Run `f` with access to a frame scoped to the lifetime of the current
    /// reference, which may be smaller than `'a`.
    pub(crate) fn with_narrowed<'child, R>(
        &'child mut self,
        f: impl FnOnce(&mut OffsetFrame<'pool, 'a, 'child>) -> R,
    ) -> R
    where
        'a: 'child,
    {
        // SAFETY: the return value of narrow() is dropped after `f` exits.
        unsafe { f(&mut self.narrow()) }
    }

    /// Replace index 'i' with 'elt'. The previous value is restored when this
    /// frame goes out of scope.
    pub(crate) fn replace(&mut self, i: usize, elt: RangeOrSlice<&'a SortedOffsetSlice>) {
        // SAFETY: data is valid for &'a, which must outlive the self's current
        // lifetime.
        let slot = unsafe { &mut *self.data }.get_mut(i).unwrap();

        // SAFETY: RangeOrSlice is repr(C), so its layout is well-defined.
        // &SortedOffset and *const SortedOffset have identical layouts, and
        // this transmute casts away a lifetime so the operation is safe.
        //
        // We also are not violating any invariants, as 'elt' is valid for 'a.
        let erased = unsafe {
            mem::transmute::<
                Slot<'pool, &'a SortedOffsetSlice>,
                Slot<'pool, *const SortedOffsetSlice>,
            >(Slot::new(elt))
        };
        let old = std::mem::replace(slot, erased);
        self.to_replace.push((i, old));
    }

    /// Get the current value at index `i`.
    pub(crate) fn get(&self, i: usize) -> Option<&Slot<'pool, &'a SortedOffsetSlice>> {
        // SAFETY: data is valid for &'a, which must outlive self.
        let data = unsafe { &*self.data };
        let res = data.get(i)?;
        // SAFETY: See the comment on layout in 'replace'.
        //
        // This Slot/RangeOrSlice is valid for 'a: it was either inserted in a
        // current or previous frame with that lifetime, or it was rolled back
        // in a frame's drop method.
        Some(unsafe {
            mem::transmute::<
                &Slot<'pool, *const SortedOffsetSlice>,
                &Slot<'pool, &'a SortedOffsetSlice>,
            >(res)
        })
    }

    pub(crate) fn iter(
        &self,
    ) -> impl Iterator<Item = (AtomId, &Slot<'pool, &'a SortedOffsetSlice>)> {
        // SAFETY: see comments in 'get'
        let data = unsafe { &*self.data };
        data.iter().enumerate().map(|(i, v)| {
            (AtomId::from_usize(i), unsafe {
                mem::transmute::<
                    &Slot<'pool, *const SortedOffsetSlice>,
                    &Slot<'pool, &'a SortedOffsetSlice>,
                >(v)
            })
        })
    }
}

impl<'pool, 'parent, 'a> ops::Index<usize> for OffsetFrame<'pool, 'parent, 'a> {
    type Output = Slot<'pool, &'a SortedOffsetSlice>;

    fn index(&self, key: usize) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<'pool, 'parent, 'a> Drop for OffsetFrame<'pool, 'parent, 'a> {
    fn drop(&mut self) {
        for (i, range) in self.to_replace.drain(..).rev() {
            // SAFETY: data must be valid for 'a, and 'range' is either valid
            // for 'parent' or will be overwritten later in 'range'.
            unsafe {
                (&mut *self.data)[i] = range;
            }
        }
    }
}

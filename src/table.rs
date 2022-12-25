//! A table type used to represent functions.
//!
//! Tables are essentially hash table mapping from vectors of values to values,
//! but they make different trade-offs than standard HashMaps or IndexMaps:
//!
//! * Like indexmap, tables preserve insertion order and support lookups based on
//! vector-like "offsets" in addition to table keys.
//!
//! * Unlike indexmap, these tables support constant-time removals that preserve
//! insertion order. Removals merely mark entries as "stale."
//!
//! These features come at the cost of needing to periodically rehash the table.
//! These rehashes must be done explicitly because they perturb the integer
//! table offsets that are otherwise stable. We prefer explicit rehashes because
//! column-level indexes use raw offsets into the table, and they need to be
//! rebuilt when a rehash happens.
//!
//! The advantage of these features is that tables can be sorted by "timestamp,"
//! making it efficient to iterate over subsets of a table matching a given
//! timestamp range.
//!
//! Note on rehashing: We will eventually want to keep old/stale entries around
//! to facilitate proofs/provenance. Early testing found that removing this in
//! the "obvious" way (keeping 'vals' around, avoiding `mem::take()`s for stale
//! entries, keeping stale entries out of `table` made some workloads very slow.
//! It's likely that we will have to store these "on the side" or use some sort
//! of persistent data-structure for the entire table.
use std::{
    alloc::{alloc, realloc, Layout},
    hash::{BuildHasher, Hash, Hasher},
    mem,
    ops::Range,
    ptr::{self},
    slice,
};

use hashbrown::raw::RawTable;
use static_assertions::const_assert;

use crate::{
    binary_search::binary_search_table_by_key, util::BuildHasher as BH, TupleOutput, Value,
};

type Offset = usize;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct TableOffset {
    // Hashes are stored inline in the table to avoid cache misses during
    // probing, and to avoid `values` lookups entirely during insertions.
    hash: u64,
    off: Offset,
}

#[derive(Clone)]
pub(crate) struct Table {
    max_ts: u32,
    n_stale: usize,
    table: RawTable<TableOffset>,
    vals: FlatVec,
}

/// Used for the RawTable probe sequence.
macro_rules! search_for {
    ($slf:expr, $hash:expr, $inp:expr) => {
        |to| {
            // Test that hashes match.
            if to.hash != $hash {
                return false;
            }
            // If the hash matches, the value should not be stale, and the data
            // should match.
            if let Some((inp, _)) = $slf.vals.get(to.off as usize) {
                inp == $inp
            } else {
                // stale
                false
            }
        }
    };
}

impl Table {
    pub(crate) fn new(arity: usize) -> Table {
        Table {
            max_ts: 0,
            n_stale: 0,
            table: Default::default(),
            vals: FlatVec::new(arity),
        }
    }
    /// Clear the contents of the table.
    pub(crate) fn clear(&mut self) {
        self.max_ts = 0;
        self.n_stale = 0;
        self.table.clear();
        self.vals.clear();
    }

    /// Indicates whether or not the table should be rehashed.
    pub(crate) fn too_stale(&self) -> bool {
        self.n_stale > (self.vals.len() / 2)
    }

    /// Rehashes the table, invalidating any offsets stored into the table.
    pub(crate) fn rehash(&mut self) {
        let mut dst = 0usize;
        self.table.clear();
        self.vals.retain_live(|inp| {
            let hash = hash_values(inp);
            self.table
                .insert(hash, TableOffset { hash, off: dst }, |to| to.hash);
            dst += 1;
        });
        self.n_stale = 0;
    }

    /// Get the entry in the table for the given values, if they are in the
    /// table.
    pub(crate) fn get(&self, inputs: &[Value]) -> Option<&TupleOutput> {
        let hash = hash_values(inputs);
        let TableOffset { off, .. } = self.table.get(hash, search_for!(self, hash, inputs))?;
        self.vals.get_output(*off)
    }

    /// Insert the given data into the table at the given timestamp. Return the
    /// previous value, if there was one.
    pub(crate) fn insert(&mut self, inputs: &[Value], out: Value, ts: u32) -> Option<Value> {
        let mut res = None;
        self.insert_and_merge(inputs, ts, |prev| {
            res = prev;
            out
        });
        res
    }

    /// Insert the given data into the table at the given timestamp. Thismethod
    /// allows for efficient 'merges', conditional on the previous value mapped
    /// to by the given index.
    ///
    /// * `on_merge(None)` should return the value mapping to the given slot.
    /// * `on_merge(Some(x))` can return a "merged" value (e.g. the union union
    ///   of `x` and `on_merge(None)`).
    pub(crate) fn insert_and_merge(
        &mut self,
        inputs: &[Value],
        ts: u32,
        on_merge: impl FnOnce(Option<Value>) -> Value,
    ) {
        assert!(ts >= self.max_ts);
        self.max_ts = ts;
        let hash = hash_values(inputs);
        if let Some(TableOffset { off, .. }) =
            self.table.get_mut(hash, search_for!(self, hash, inputs))
        {
            let hdr = self.vals.header_mut(*off);
            debug_assert!(hdr.live());
            let next = on_merge(Some(hdr.out.value));
            if next.bits == hdr.out.value.bits {
                return;
            }
            hdr.stale_ts = ts;
            self.n_stale += 1;
            let new_offset = self.vals.len();
            self.vals.push(ts, inputs, next);
            *off = new_offset;
            return;
        }
        let new_offset = self.vals.len();
        self.vals.push(ts, inputs, on_merge(None));
        self.table.insert(
            hash,
            TableOffset {
                hash,
                off: new_offset,
            },
            |off| off.hash,
        );
    }

    /// One more than the maximum (potentially) valid offset into the table.
    pub(crate) fn len(&self) -> usize {
        self.vals.len()
    }

    /// Whether the table is completely empty, including stale entries.
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The minimum timestamp stored by the table, if there is one.
    pub(crate) fn min_timestamp(&self) -> Option<u32> {
        self.vals.min_timestamp()
    }

    /// An upper bound for all timestamps stored in the table.
    pub(crate) fn max_ts(&self) -> u32 {
        self.max_ts
    }

    /// Get the timestamp for the entry at index `i`.
    pub(crate) fn get_timestamp(&self, i: usize) -> u32 {
        self.vals.get_timestamp(i)
    }

    /// Remove the given mapping from the table, returns whether an entry was
    /// removed.
    pub(crate) fn remove(&mut self, inp: &[Value], ts: u32) -> bool {
        let hash = hash_values(inp);
        let entry = if let Some(entry) = self.table.remove_entry(hash, search_for!(self, hash, inp))
        {
            entry
        } else {
            return false;
        };
        self.n_stale += self.vals.set_stale(entry.off, ts) as usize;
        true
    }

    /// Remove the entry at the given offset from the table.
    pub(crate) fn remove_index(&mut self, i: usize, ts: u32) {
        self.n_stale += self.vals.set_stale(i, ts) as usize;
    }

    /// Returns the entries at the given index if the entry is live and the index in bounds.
    pub(crate) fn get_index(&self, i: usize) -> Option<(&[Value], &TupleOutput)> {
        self.vals.get(i)
    }

    /// Iterate over the live entries in the table, in insertion order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&[Value], &TupleOutput)> + '_ {
        self.iter_range(0..self.len()).map(|(_, y, z)| (y, z))
    }

    /// Iterate over the live entries in the offset range, passing back the
    /// offset corresponding to each entry.
    pub(crate) fn iter_range(
        &self,
        range: Range<usize>,
    ) -> impl Iterator<Item = (usize, &[Value], &TupleOutput)> + '_ {
        self.vals.iter_range(range)
    }

    #[cfg(debug_assertions)]
    pub(crate) fn assert_sorted(&self) {
        let ts = Vec::from_iter((0..self.vals.len()).map(|x| self.vals.get_timestamp(x)));
        assert!(ts.windows(2).all(|xs| xs[0] <= xs[1]));
    }

    /// Iterate over the live entries in the timestamp range, passing back their
    /// offset into the table.
    pub(crate) fn iter_timestamp_range(
        &self,
        range: &Range<u32>,
    ) -> impl Iterator<Item = (usize, &[Value], &TupleOutput)> + '_ {
        let indexes = self.transform_range(range);
        self.iter_range(indexes)
    }

    /// Return the approximate number of entries in the table for the given
    /// timestamp range.
    pub(crate) fn approximate_range_size(&self, range: &Range<u32>) -> usize {
        let indexes = self.transform_range(range);
        indexes.end - indexes.start
    }

    /// Transform a range of timestamps to the corresponding range of indexes
    /// into the table.
    pub(crate) fn transform_range(&self, range: &Range<u32>) -> Range<usize> {
        if let Some(start) = binary_search_table_by_key(self, range.start) {
            if let Some(end) = binary_search_table_by_key(self, range.end) {
                start..end
            } else {
                start..self.len()
            }
        } else {
            0..0
        }
    }
}

fn hash_values(vs: &[Value]) -> u64 {
    // Just hash the bits: all inputs to the same function should have matching
    // column types.
    let mut hasher = BH::default().build_hasher();
    for v in vs {
        v.bits.hash(&mut hasher);
    }
    hasher.finish()
}

#[derive(Copy, Clone)]
struct TupleHeader {
    out: TupleOutput,
    stale_ts: u32,
}

impl TupleHeader {
    const fn size_of_entry(arity: usize) -> usize {
        // NB: the code for FlatVec relies on the fact that TupleHeader has a trivial drop!
        const_assert!(!mem::needs_drop::<TupleHeader>());
        const_assert!(mem::align_of::<TupleHeader>() == mem::align_of::<Value>());
        mem::size_of::<TupleHeader>() + (arity * mem::size_of::<Value>())
    }

    fn live(&self) -> bool {
        self.stale_ts == u32::MAX
    }
}

struct FlatVec {
    arity: usize,
    len: usize,
    capacity: usize,
    data: *mut u8,
}
impl Clone for FlatVec {
    fn clone(&self) -> FlatVec {
        let populated_bytes = self.len * self.entry_size();
        let data = unsafe {
            let new_alloc = alloc(
                Layout::from_size_align(populated_bytes, mem::align_of::<TupleHeader>()).unwrap(),
            );
            ptr::copy_nonoverlapping(self.data, new_alloc, populated_bytes);
            new_alloc
        };
        FlatVec {
            arity: self.arity,
            len: self.len,
            capacity: self.len,
            data,
        }
    }
}

impl FlatVec {
    fn new(arity: usize) -> FlatVec {
        FlatVec {
            arity,
            len: 0,
            capacity: 0,
            data: ptr::null_mut(),
        }
    }

    fn clear(&mut self) {
        self.len = 0;
    }

    fn retain_live(&mut self, mut f: impl FnMut(&[Value])) {
        let mut write_head = 0;
        let entry_size = self.entry_size();
        // The implementation of 'retain' in the standard library is much more
        // complex, but most of the complexity there has to do with drops. We
        // don't worry about drops here because Value drops are trivial.
        for i in 0..self.len {
            unsafe {
                // SAFETY: `i` is in-bounds.
                let hdr = &*self.header_unchecked(i);
                if !hdr.live() {
                    continue;
                }
                if write_head != i {
                    // SAFETY: we have nonoverlapping pointers because write_head != i
                    ptr::copy_nonoverlapping(
                        hdr as *const TupleHeader as *const u8,
                        self.header_unchecked(write_head) as *mut u8,
                        entry_size,
                    )
                }
                // SAFETY: hdr is a valid pointer.
                let vals = self.inputs_from_header(hdr);
                f(vals);
                write_head += 1
            }
        }
        self.len = write_head;
    }

    fn min_timestamp(&self) -> Option<u32> {
        if self.is_empty() {
            None
        } else {
            Some(self.header(0).out.timestamp)
        }
    }

    fn push(&mut self, ts: u32, ins: &[Value], out: Value) {
        assert_eq!(ins.len(), self.arity);
        if self.len == self.capacity {
            self.grow();
        }
        let raw = self.data as *mut u8;
        unsafe {
            // SAFETY: addr now points in bounds (the call to grow guarantees that len < capacity)
            let addr = raw.add(TupleHeader::size_of_entry(self.arity) * self.len);
            let header = addr as *mut TupleHeader;
            // SAFETY: TupleHeader has a trivial drop method, and the pointer is in-bounds
            header.write(TupleHeader {
                out: TupleOutput {
                    value: out,
                    timestamp: ts,
                },
                stale_ts: !0,
            });
            // SAFETY: We aways reserve entry_size() capacity, so if `addr` is in-bounds, then so is `dst`
            let dst = addr.add(mem::size_of::<TupleHeader>());
            // SAFETY:
            //  * ins has `arity` entries due to assertion at the top of the function
            //  * `dst` has `arity` entries due to the calls to realloc always
            //    ocurreing in multiples of entry_size()
            //  * The two cannot overlap becase `dst` is currently uninitialized memory.
            ptr::copy_nonoverlapping(ins.as_ptr(), dst as *mut Value, self.arity);
        }
        self.len += 1;
    }

    /// Get the contents of the tuple at this slot. Returns nothing if the value
    /// was stale.
    ///
    /// # Panics
    /// This method will panic if `i` is out of bounds.
    fn get(&self, i: usize) -> Option<(&[Value], &TupleOutput)> {
        let hdr = self.header(i);
        if !hdr.live() {
            return None;
        }
        // SAFETY: `hdr` points into `self`.
        let inputs = unsafe { self.inputs_from_header(hdr) };
        Some((inputs, &hdr.out))
    }

    /// Extract the inputs directly past the given header.
    ///
    /// # Safety
    /// Callers should only pass a header that points into `self`
    unsafe fn inputs_from_header<'a>(&'a self, hdr: &'a TupleHeader) -> &'a [Value] {
        // NB: we've checked that the header is in bounds, and we
        // reserve a full entry_size() amount of space per slot.
        let addr = (hdr as *const TupleHeader).add(1) as *const Value;
        slice::from_raw_parts(addr, self.arity)
    }

    /// Like `get`, but only gets the output component of an entry.
    fn get_output(&self, i: usize) -> Option<&TupleOutput> {
        let hdr = self.header(i);
        if !hdr.live() {
            return None;
        }
        Some(&hdr.out)
    }

    /// Like `get_output`, but only returns the timestamp field and will return
    /// the correct write timestamp for a stale entry. This is used for
    /// implementing binary search.
    ///
    /// # Panics
    /// This method panics if `i` is not in-bounds.
    fn get_timestamp(&self, i: usize) -> u32 {
        self.header(i).out.timestamp
    }

    fn len(&self) -> usize {
        self.len
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn set_stale(&mut self, i: usize, ts: u32) -> bool {
        let hdr = self.header_mut(i);
        let newly_stale = hdr.live();
        hdr.stale_ts = ts;
        newly_stale
    }

    fn header_raw(&self, i: usize) -> *mut TupleHeader {
        // SAFETY: this assertion guarantees that 'add' returns a valid address.
        assert!(i < self.len);
        unsafe { self.header_unchecked(i) }
    }

    unsafe fn header_unchecked(&self, i: usize) -> *mut TupleHeader {
        self.data.add(self.entry_size() * i) as *mut TupleHeader
    }

    fn header(&self, i: usize) -> &TupleHeader {
        // SAFETY: header_raw checks that `i` is in-bounds, and the entry will
        // remain valid for the duration of the function.
        unsafe { &*self.header_raw(i) }
    }
    fn header_mut(&mut self, i: usize) -> &mut TupleHeader {
        // SAFETY: header_raw checks that `i` is in-bounds, and the entry will
        // remain valid for the duration of the function.
        unsafe { &mut *self.header_raw(i) }
    }

    fn iter_range(
        &self,
        range: Range<usize>,
    ) -> impl Iterator<Item = (usize, &[Value], &TupleOutput)> + '_ {
        let range = if range.start >= self.len {
            0..0
        } else {
            range.start..range.end.min(self.len)
        };
        range.filter_map(move |i| {
            // We did bounds-checking once at the top of the method. Unsafe accesses are good.
            unsafe {
                let hdr = &*self.header_unchecked(i);
                if hdr.live() {
                    Some((i, self.inputs_from_header(hdr), &hdr.out))
                } else {
                    None
                }
            }
        })
    }

    fn grow(&mut self) {
        let next_capacity = if self.capacity == 0 {
            1
        } else {
            self.capacity * 2
        };
        unsafe {
            self.data = realloc(
                self.data,
                Layout::from_size_align(
                    self.entry_size() * self.capacity,
                    mem::align_of::<TupleHeader>(),
                )
                .unwrap(),
                self.entry_size() * next_capacity,
            )
        }
        self.capacity = next_capacity;
    }

    fn entry_size(&self) -> usize {
        TupleHeader::size_of_entry(self.arity)
    }
}

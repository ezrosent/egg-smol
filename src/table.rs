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
    alloc::{realloc, Layout},
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
    ValueVec,
};

type Offset = usize;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct TableOffset {
    // Hashes are stored inline in the table to avoid cache misses during
    // probing, and to avoid `values` lookups entirely during insertions.
    hash: u64,
    off: Offset,
}

struct TupleHeader {
    write_ts: u32,
    stale_ts: u32,
    out: Value,
}

impl TupleHeader {
    const fn size_of_entry(arity: usize) -> usize {
        const_assert!(mem::align_of::<TupleHeader>() == mem::align_of::<Value>());
        mem::size_of::<TupleHeader>() + (arity * mem::size_of::<Value>())
    }
}

struct FlatVec {
    arity: usize,
    len: usize,
    capacity: usize,
    data: *mut u8,
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
                write_ts: ts,
                stale_ts: !0,
                out,
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
    fn get(&self, i: usize) -> Option<(&[Value], &Value, u32)> {
        let hdr = self.header(i);
        if hdr.stale_ts != u32::MAX {
            return None;
        }
        let inputs = unsafe {
            // SAFETY: we've checked that the header is in bounds, and we
            // reserve a full entry_size() amount of space per slot.
            let addr = (hdr as *const TupleHeader).add(1) as *const Value;
            slice::from_raw_parts(addr, self.arity)
        };
        Some((inputs, &hdr.out, hdr.write_ts))
    }

    fn set_stale(&mut self, i: usize, ts: u32) {
        self.header_mut(i).stale_ts = ts;
    }

    fn header_raw(&self, i: usize) -> *mut TupleHeader {
        // SAFETY: this assertion guarantees that 'add' returns a valid address.
        assert!(i < self.len);
        unsafe { self.data.add(self.entry_size() * i) as *mut TupleHeader }
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

#[derive(Default, Clone)]
pub(crate) struct Table {
    max_ts: u32,
    n_stale: usize,
    table: RawTable<TableOffset>,
    vals: Vec<(Input, TupleOutput)>,
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
            let inp = &$slf.vals[to.off as usize].0;
            inp.live() && inp.data() == $inp
        }
    };
}

impl Table {
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
        let mut src = 0usize;
        let mut dst = 0usize;
        self.table.clear();
        self.vals.retain(|(inp, _)| {
            if inp.live() {
                let hash = hash_values(inp.data());
                self.table
                    .insert(hash, TableOffset { hash, off: dst }, |to| to.hash);
                src += 1;
                dst += 1;
                true
            } else {
                src += 1;
                false
            }
        });
        self.n_stale = 0;
    }

    /// Get the entry in the table for the given values, if they are in the
    /// table.
    pub(crate) fn get(&self, inputs: &[Value]) -> Option<&TupleOutput> {
        let hash = hash_values(inputs);
        let TableOffset { off, .. } = self.table.get(hash, search_for!(self, hash, inputs))?;
        debug_assert!(self.vals[*off].0.live());
        Some(&self.vals[*off].1)
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
            let (inp, prev) = &mut self.vals[*off];
            let next = on_merge(Some(prev.value));
            if next == prev.value {
                return;
            }
            inp.stale_at = ts;
            self.n_stale += 1;
            let k = mem::take(&mut inp.data);
            let new_offset = self.vals.len();
            self.vals.push((
                Input::new(k),
                TupleOutput {
                    value: next,
                    timestamp: ts,
                },
            ));
            *off = new_offset;
            return;
        }
        let new_offset = self.vals.len();
        self.vals.push((
            Input::new(inputs.into()),
            TupleOutput {
                value: on_merge(None),
                timestamp: ts,
            },
        ));
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
    pub(crate) fn min_ts(&self) -> Option<u32> {
        Some(self.vals.first()?.1.timestamp)
    }

    /// An upper bound for all timestamps stored in the table.
    pub(crate) fn max_ts(&self) -> u32 {
        self.max_ts
    }

    /// Get the timestamp for the entry at index `i`.
    pub(crate) fn get_timestamp(&self, i: usize) -> Option<u32> {
        Some(self.vals.get(i)?.1.timestamp)
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
        self.vals[entry.off].0.stale_at = ts;
        self.n_stale += 1;
        true
    }

    /// Remove the entry at the given offset from the table.
    pub(crate) fn remove_index(&mut self, i: usize, ts: u32) {
        let (inp, _) = &mut self.vals[i];
        if inp.live() {
            inp.stale_at = ts;
            self.n_stale += 1;
        }
    }

    /// Returns the entries at the given index if the entry is live and the index in bounds.
    pub(crate) fn get_index(&self, i: usize) -> Option<(&[Value], &TupleOutput)> {
        let (inp, out) = self.vals.get(i)?;
        if !inp.live() {
            return None;
        }
        Some((inp.data(), out))
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
        self.vals[range.clone()]
            .iter()
            .zip(range)
            .filter_map(|((inp, out), i)| {
                if inp.live() {
                    Some((i, inp.data(), out))
                } else {
                    None
                }
            })
    }

    #[cfg(debug_assertions)]
    pub(crate) fn assert_sorted(&self) {
        assert!(self
            .vals
            .windows(2)
            .all(|xs| xs[0].1.timestamp <= xs[1].1.timestamp))
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct Input {
    data: ValueVec,
    /// The timestamp at which the given input became "stale"
    stale_at: u32,
}

impl Input {
    fn new(data: ValueVec) -> Input {
        Input {
            data,
            stale_at: u32::MAX,
        }
    }

    fn data(&self) -> &[Value] {
        self.data.as_slice()
    }

    fn live(&self) -> bool {
        self.stale_at == u32::MAX
    }
}

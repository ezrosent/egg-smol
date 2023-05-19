//! A timestamped collection of values.
use std::{
    cmp, fmt,
    hash::{Hash, Hasher},
    mem, slice,
};

use hashbrown::raw::RawTable;
use rustc_hash::FxHasher;

use crate::{
    common::{HashMap, IndexSet, NumericId},
    define_id,
    free_join::AtomIdx,
    function::offsets::Offsets,
    pool::{Pool, PoolRef, PoolSet},
    schema::{ColumnTy, Schema},
    uf::{UnionFind, UpdateTrackingUnionFind},
};

use super::{
    offsets::{Offset, OffsetRange},
    Value,
};

define_id!(pub(crate) Timestamp, u32);
define_id!(pub(crate) Generation, u32, "the generation of a table. Offsets are only valid within a generation");
define_id!(
    RawOffset,
    usize,
    "a raw offset into a table, not divided by arity+1"
);

/// Hashtable entries pointing into the offsets of a table.
///
/// This is `pub(crate)` to hook it into the memory pooling system.
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct TableEntry {
    hashcode: u64,
    offset: RawOffset,
}

/// An index maintained on a table to support incremental rebuilding.
struct RebuildIndex<'a> {
    data: HashMap<Value, PoolRef<'a, IndexSet<Offset>>>,
    covered_up_to: Offset,
    index_cols: Vec<AtomIdx>,
    index_ret: bool,
    set_pool: &'a Pool<IndexSet<Offset>>,
    update_pool: &'a Pool<Vec<(TableEntry, TableEntry)>>,
}

impl<'a> RebuildIndex<'a> {
    fn new(
        set_pool: &'a Pool<IndexSet<Offset>>,
        update_pool: &'a Pool<Vec<(TableEntry, TableEntry)>>,
        schema: &Schema,
    ) -> Self {
        let index_cols = schema
            .args()
            .iter()
            .enumerate()
            .filter_map(|(col, ty)| match ty {
                ColumnTy::Id => Some(AtomIdx::from_usize(col)),
                ColumnTy::Primitive(_) => None,
            })
            .collect();
        let index_ret = match schema.ret() {
            ColumnTy::Id => true,
            ColumnTy::Primitive(_) => false,
        };
        Self {
            data: HashMap::default(),
            covered_up_to: Offset::new(0),
            index_cols,
            index_ret,
            set_pool,
            update_pool,
        }
    }

    fn insert(&mut self, val: Value, offset: Offset) {
        let pool = self.set_pool;
        self.data
            .entry(val)
            .or_insert_with(|| pool.get_default())
            .insert(offset);
    }

    fn clear(&mut self) {
        self.data.clear();
        self.covered_up_to = Offset::new(0);
    }

    fn move_out(&mut self) -> RebuildIndex<'a> {
        let mut new = RebuildIndex::new(
            self.set_pool,
            self.update_pool,
            &Schema::new(std::iter::empty(), ColumnTy::Id),
        );
        mem::swap(&mut new, self);
        new
    }
}

/// Core data for a [`Table`]. This is its own struct to allow other fields in
/// [`Table`] to be mutably borrowed while calling methods on this struct.
struct TableData {
    data: Vec<Value>,
    arity: usize,
    total_offsets: usize,
    stale: usize,
    next_stale_threshold: usize,
}

impl TableData {
    fn get_key(&self, o: RawOffset) -> &[Value] {
        let i = o.index();
        &self.data[i + 1..i + self.arity + 1]
    }

    fn get_value_mut(&mut self, o: RawOffset) -> &mut Value {
        &mut self.data[o.index()]
    }

    fn set_stale(&mut self, o: RawOffset) {
        let v = self.get_value_mut(o);
        let was = v.is_stale();
        self.get_value_mut(o).set_stale();
        if !was {
            self.stale += 1;
        }
    }

    fn get_value(&self, o: RawOffset) -> &Value {
        &self.data[o.index()]
    }

    fn get_key_value_mut(&mut self, o: RawOffset) -> (&mut [Value], &mut Value) {
        let i = o.index();
        let (v, ks) = self.data[i..i + self.arity + 1].split_first_mut().unwrap();
        (ks, v)
    }

    fn push(&mut self, ks: &[Value], v: Value) {
        self.data.reserve(self.arity + 1);
        self.data.push(v);
        self.data.extend_from_slice(ks);
        self.total_offsets += 1;
    }

    unsafe fn get_key_value_unchecked(&self, off: Offset) -> (&[Value], Value) {
        debug_assert!(off.index() < self.data.len());
        let off = into_raw(off, self.arity).index();
        let val_ptr = self.data.as_ptr().add(off);
        let key_ptr = val_ptr.add(1);
        (slice::from_raw_parts(key_ptr, self.arity), *val_ptr)
    }

    /// Canonicalize the entry at `off` in place.
    ///
    /// Returns the old and new table entries if any values were changed.
    fn canon_in_place(
        &mut self,
        off: Offset,
        cols: &[AtomIdx],
        ret: bool,
        uf: &mut UnionFind<Value>,
    ) -> Option<(TableEntry, TableEntry)> {
        let mut changed = false;
        let raw_offset = into_raw(off, self.arity);
        let (key, val) = self.get_key_value_mut(raw_offset);
        let old = TableEntry {
            hashcode: hash_slice(key),
            offset: raw_offset,
        };
        for ix in cols {
            let old = key[ix.index()];
            let new = uf.find(old);
            if old != new {
                changed = true;
                key[ix.index()] = new;
            }
        }
        if ret {
            let new = uf.find(*val);
            if *val != new {
                changed = true;
                *val = new;
            }
        }
        if changed {
            let new = TableEntry {
                hashcode: hash_slice(key),
                offset: raw_offset,
            };
            Some((old, new))
        } else {
            None
        }
    }

    /// Take the entry starting at `off` and append a copy to the end of the
    /// table, returning the start offset of this new entry.
    ///
    /// The old entry is marked as stale.
    fn promote(&mut self, off: RawOffset) -> RawOffset {
        let old_len = self.data.len();
        self.data
            .resize_with(old_len + self.arity + 1, || Value::new(0));
        self.data
            .copy_within(off.index()..(off.index() + self.arity + 1), old_len);
        self.set_stale(off);
        self.total_offsets += 1;
        RawOffset::new(old_len)
    }

    /// Canonicalize the entry at `off` by moving it to the front of `data`,
    /// including marking the old copy as stale.
    ///
    /// Returns the old and new table entries if any values were changed.
    fn canon_copy(
        &mut self,
        off: Offset,
        next_offset: Offset,
        cols: &[AtomIdx],
        ret: bool,
        uf: &mut UnionFind<Value>,
    ) -> Option<(TableEntry, TableEntry)> {
        let (old, mut new) = self.canon_in_place(off, cols, ret, uf)?;
        let raw_offset = into_raw(off, self.arity);
        let new_offset = self.promote(raw_offset);
        debug_assert_eq!(into_raw(next_offset, self.arity), new_offset);
        new.offset = new_offset;
        Some((old, new))
    }
}

pub(crate) struct Table<'a> {
    generation: Generation,
    timestamp_offsets: Vec<(Timestamp, Offset)>,
    data: TableData,
    hash: RawTable<TableEntry>,
    rebuild_index: RebuildIndex<'a>,
}

impl<'a> fmt::Debug for Table<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let chunks: Vec<(usize, &[Value])> = self
            .data
            .data
            .chunks(self.arity() + 1)
            .enumerate()
            .collect();
        f.debug_struct("Table")
            .field("generation", &self.generation)
            .field("stale", &self.data.stale)
            .field("arity", &self.data.arity)
            .field("timestamp_offsets", &self.timestamp_offsets)
            .field("total_offsets", &self.data.total_offsets)
            .field("data", &chunks)
            .field("hash", &"...")
            .finish()
    }
}

macro_rules! search_for {
    ($table:expr, $hash:expr, $key:expr) => {
        |entry| entry.hashcode == $hash && $table.data.get_key(entry.offset) == $key
    };
}

impl<'a> Table<'a> {
    pub(crate) fn new(schema: &Schema, ts: Timestamp, pool_set: &PoolSet<'a>) -> Self {
        let arity = schema.arity();
        Self {
            generation: Generation::from_usize(0),
            timestamp_offsets: vec![(ts, Offset::new(0))],
            data: TableData {
                data: Vec::new(),
                arity,
                total_offsets: 0,
                stale: 0,
                next_stale_threshold: 100,
            },
            hash: RawTable::new(),
            rebuild_index: RebuildIndex::new(pool_set.get(), pool_set.get(), schema),
        }
    }

    /// The current generation of the table.
    pub(crate) fn generation(&self) -> Generation {
        self.generation
    }

    /// The arity of the function encoded by the table.
    pub(crate) fn arity(&self) -> usize {
        self.data.arity
    }

    /// One past the maximum safe offset into the table
    pub(crate) fn offset_limit(&self) -> Offset {
        Offset::from_usize(self.data.total_offsets)
    }

    pub(crate) fn last_changed(&self) -> Timestamp {
        self.timestamp_offsets.last().unwrap().0
    }

    pub(crate) fn insert(&mut self, key: &[Value], mut merge: impl FnMut(Option<Value>) -> Value) {
        assert_eq!(key.len(), self.arity());
        let hash = hash_slice(key);
        let to_insert = if let Some(entry) = self.hash.get_mut(hash, search_for!(self, hash, key)) {
            // The key is present in the map. A few cases to consider.
            let prev = *self.data.get_value(entry.offset);
            let res = merge(Some(prev));
            if res == prev {
                // No change
                return;
            } else {
                // There's a change, but for a previous timestamp. We need to add a new entry.
                self.data.set_stale(entry.offset);
                entry.offset = RawOffset::new(self.data.data.len());
                res
            }
        } else {
            // Insert a new entry.
            self.hash.insert_entry(
                hash,
                TableEntry {
                    hashcode: hash,
                    offset: RawOffset::new(self.data.data.len()),
                },
                |entry| entry.hashcode,
            );
            merge(None)
        };
        assert!(
            !to_insert.is_stale(),
            "attempting to insert a stale entry into a table (id overflow?)"
        );
        self.data.push(key, to_insert);
        self.maybe_rehash();
    }

    pub(crate) fn get(&self, key: &[Value]) -> Option<Value> {
        let hash = hash_slice(key);
        let entry = self.hash.get(hash, search_for!(self, hash, key))?;
        let res = self.data.data[entry.offset.index()];
        debug_assert!(!res.is_stale());
        Some(res)
    }

    pub(crate) fn remove(&mut self, key: &[Value]) -> bool {
        let hash = hash_slice(key);
        let Some(entry) = self.hash.remove_entry(hash, search_for!(self, hash, key)) else { 
            return false;
        };
        self.data.set_stale(entry.offset);
        true
    }

    /// Incrementally canonicalize all entries in the table using the `recent`
    /// set from `tracking_uf`.
    pub(crate) fn rebuild(
        &mut self,
        ts: Timestamp,
        tracking_uf: &mut UpdateTrackingUnionFind<Value>,
        mut merge: impl FnMut(&mut UnionFind<Value>, Value, Value) -> Value,
    ) {
        if tracking_uf.recent_reparents.is_empty()
            || (self.rebuild_index.index_cols.is_empty() && !self.rebuild_index.index_ret)
        {
            return;
        }

        self.update_timestamp(ts);
        self.update_rebuild_index();
        let mut updates = self.rebuild_index.update_pool.get_default();
        macro_rules! process_entries {
            ($entries:expr) => {
                for offset in $entries.iter().copied() {
                    let raw = into_raw(offset, self.arity());
                    if self.data.get_value(raw).is_stale() {
                        continue;
                    }
                    let next_offset = self.offset_limit();
                    let Some(update) = self.data.canon_copy(
                                                        offset,
                                                        next_offset,
                                                        &self.rebuild_index.index_cols,
                                                        self.rebuild_index.index_ret,
                                                        &mut tracking_uf.uf,
                                                    ) else { continue; };
                    updates.push(update);
                }
            };
        }
        if tracking_uf.recent_reparents.len() < self.rebuild_index.data.len() {
            for v in &tracking_uf.recent_reparents {
                let Some(entries) = self.rebuild_index.data.get(v)  else {
                    continue;
                };
                process_entries!(entries);
            }
        } else {
            for (v, entries) in &self.rebuild_index.data {
                if !tracking_uf.recent_reparents.contains(v) {
                    continue;
                }
                process_entries!(entries);
            }
        }
        for (old, mut new) in updates.drain(..) {
            // First, remove the old entry:
            self.hash.remove_entry(old.hashcode, |entry| entry == &old);
            let new_ks = self.data.get_key(new.offset);
            // Then, check if the new entry is already present:
            if let Some(cur) = self
                .hash
                .remove_entry(new.hashcode, search_for!(self, new.hashcode, new_ks))
            {
                // Merge the values. Remove 'cur'. Write the merged value to 'new'.

                // NB: it would be more efficient to mark the smaller offset as
                // stale, because the larger offset has a better chance of
                // supporting an in-place update.
                let cur_v_mut = self.data.get_value_mut(cur.offset);
                let cur_v = *cur_v_mut;
                if !cur_v.is_stale() {
                    cur_v_mut.set_stale();
                    self.data.stale += 1;

                    let new_v = self.data.get_value_mut(new.offset);

                    let merged = merge(&mut tracking_uf.uf, cur_v, *new_v);
                    let changed = merged != *new_v;
                    *new_v = merged;

                    if changed {
                        new.offset = self.data.promote(new.offset);
                    }
                }
            }
            self.hash
                .insert_entry(new.hashcode, new, |entry| entry.hashcode);
        }

        self.maybe_rehash();
    }

    fn update_rebuild_index(&mut self) {
        // Round down to the beginning of the timestamp for 'covered_up_to': we
        // may have done some in-place updates within that timestamp; we need to
        // re-scan those.
        let (_, off) = match self
            .timestamp_offsets
            .binary_search_by_key(&self.rebuild_index.covered_up_to, |(_, off)| *off)
        {
            Ok(i) => self.timestamp_offsets[i],
            Err(i) => self.timestamp_offsets[i.saturating_sub(1)],
        };
        let remaining = OffsetRange::new(off, self.offset_limit());
        // NB: this works: we should avoid the in-place updates.
        // let remaining = OffsetRange::new(Offset::new(0), self.offset_limit());
        let mut rebuild_table = self.rebuild_index.move_out();
        let cols = mem::take(&mut rebuild_table.index_cols);
        remaining.iter_table(self, |offset, ks, v| {
            for ix in &cols {
                rebuild_table.insert(ks[ix.index()], offset);
            }
            if rebuild_table.index_ret {
                rebuild_table.insert(v, offset);
            }
        });
        rebuild_table.index_cols = cols;
        self.rebuild_index = rebuild_table;
        self.rebuild_index.covered_up_to = self.offset_limit();
    }

    /// Get the entry in the table at the given offset.
    ///
    /// Safety:
    /// This method performs no bounds-checks. The caller must ensure that
    /// `offset` does not exceed `max_offset`.
    pub(crate) unsafe fn get_offset_unchecked(&self, offset: Offset) -> (&[Value], Value) {
        self.data.get_key_value_unchecked(offset)
    }

    pub(crate) fn len(&self) -> usize {
        self.hash.len()
    }

    /// Iterate over the contents of the table.
    ///
    /// This routine is maintly used for tests; most other instances of
    /// iteration use specific offsets into a table.
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&[Value], Value)> {
        self.data.data.chunks(self.arity() + 1).filter_map(|chunk| {
            debug_assert_eq!(chunk.len(), self.arity() + 1);
            let value = chunk[0];
            if value.is_stale() {
                None
            } else {
                Some((&chunk[1..], value))
            }
        })
    }

    pub(crate) fn timestamp_range(&self, low: Timestamp, hi: Timestamp) -> OffsetRange {
        let start = self.get_data_offset(low);
        let end = self.get_data_offset(hi);
        OffsetRange::new(start, end)
    }

    /// Get the minimum offset in 'data' with a timestamp greater than or equal
    /// to 'ts'. If no such entry is >= 'ts', return the length of 'data'.
    fn get_data_offset(&self, ts: Timestamp) -> Offset {
        let timestamps_off = match self
            .timestamp_offsets
            .binary_search_by_key(&ts, |(ts, _)| *ts)
        {
            Ok(off) | Err(off) => off,
        };
        if let Some((_, off)) = self.timestamp_offsets.get(timestamps_off) {
            *off
        } else {
            debug_assert_eq!(
                self.data.total_offsets * (self.arity() + 1),
                self.data.data.len()
            );
            self.offset_limit()
        }
    }

    pub(crate) fn update_timestamp(&mut self, timestamp: Timestamp) {
        let target = self.offset_limit();
        let (last_ts, last_off) = self
            .timestamp_offsets
            .last_mut()
            .expect("timestamps should not be empty");
        assert!(
            *last_ts <= timestamp,
            "attempting to update table at {last_ts:?} to {timestamp:?}, which is lower"
        );
        if timestamp == *last_ts {
            return;
        }
        if *last_off == target {
            *last_ts = timestamp;
            return;
        }
        self.timestamp_offsets.push((timestamp, target));
    }

    fn maybe_rehash(&mut self) {
        if self.data.stale < self.data.next_stale_threshold {
            return;
        }
        self.data.next_stale_threshold = cmp::max(100, self.hash.len() * 2);
        self.rehash()
    }

    /// Clear out any stale entries in the table.
    fn rehash(&mut self) {
        // Remapping offsets
        let mut new_offset = 0;
        let mut old_offset = 0;
        let mut remove_counter = 0;
        let mut next_offset = 0;
        let mut target_old_offset = 0;
        let mut consume_counter = 0;
        let mut scratch = Vec::with_capacity(self.arity() + 1);
        let mut old_total = 0;

        let mut tracker = TimestampTracker::new(mem::take(&mut self.timestamp_offsets));
        let arity = self.arity();
        self.data.data.retain(|v| {
            let old = old_offset;
            old_offset += 1;
            if remove_counter > 0 {
                // The current entry is stale.
                remove_counter -= 1;
                return false;
            }
            if consume_counter > 0 {
                // We're in the process of inserting a new entry.
                consume_counter -= 1;
                new_offset += 1;
                scratch.push(*v);
                // We've filled up a scratch buffer, so we can remap the table.
                if consume_counter == 0 {
                    debug_assert_eq!(scratch.len(), arity);
                    let hash = hash_slice(&scratch);
                    self.hash
                        .get_mut(hash, |entry| {
                            entry.hashcode == hash
                                && entry.offset == RawOffset::new(target_old_offset)
                        })
                        .unwrap()
                        .offset = RawOffset::new(next_offset);
                    scratch.clear();
                }
                return true;
            }
            let prev_old_total = old_total;
            old_total += 1;
            if v.is_stale() {
                remove_counter = arity;
                return false;
            }
            // We're keeping a new entry.
            consume_counter = arity;
            next_offset = new_offset;
            tracker.advance(prev_old_total);
            target_old_offset = old;
            new_offset += 1;
            true
        });
        let (timestamp_offsets, total) = tracker.finish();
        self.timestamp_offsets = timestamp_offsets;
        self.data.stale = 0;
        self.data.total_offsets = total;
        debug_assert_eq!(
            self.data.total_offsets * (self.arity() + 1),
            self.data.data.len()
        );
        self.rebuild_index.clear();
        self.generation = Generation::from_usize(self.generation.index() + 1);
    }
}

fn hash_slice(vs: &[Value]) -> u64 {
    let mut hasher = FxHasher::default();
    for v in vs {
        v.hash(&mut hasher);
    }
    hasher.finish()
}

// various helpers for table operations, these aren't methods; instead they
// explicitly take the fields that they require as parameters, to help the
// borrow checker.

fn into_raw(off: Offset, arity: usize) -> RawOffset {
    RawOffset::from_usize(off.index() * (arity + 1))
}

/// A helper for remapping the timestamps vector during a rehash.
///
/// TimestampTracker is fed offsets from the old table and new table and fills
/// in the equivalent mappings.
struct TimestampTracker {
    old_timestamps: Vec<(Timestamp, Offset)>,
    new_timestamps: Vec<(Timestamp, Offset)>,
    next_offset: usize, // points to old_timestamps
    counter: usize,
}

impl TimestampTracker {
    fn new(old_timestamps: Vec<(Timestamp, Offset)>) -> Self {
        let len = old_timestamps.len();
        Self {
            old_timestamps,
            new_timestamps: Vec::with_capacity(len),
            next_offset: 0,
            counter: 0,
        }
    }
    fn advance(&mut self, old_offset: usize) {
        let new_offset = self.counter;
        self.counter += 1;
        let mut to_update = None;
        while let Some((ts, off)) = self.old_timestamps.get(self.next_offset) {
            if old_offset >= off.index() {
                self.next_offset += 1;
                to_update = Some(*ts);
            } else {
                break;
            }
        }
        if let Some(to_update) = to_update {
            self.new_timestamps
                .push((to_update, Offset::from_usize(new_offset)));
        }
    }
    fn finish(self) -> (Vec<(Timestamp, Offset)>, usize) {
        (self.new_timestamps, self.counter)
    }
}

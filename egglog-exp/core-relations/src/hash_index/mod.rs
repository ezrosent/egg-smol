//! Indexes on specific projections of tables.
use std::{
    hash::{Hash, Hasher},
    mem,
};

use hashbrown::raw::RawTable;
use numeric_id::{define_id, NumericId};
use rustc_hash::FxHasher;

use crate::{
    common::{IndexMap, Value},
    offsets::{RowId, SortedOffsetSlice, SubsetRef},
    pool::{Clear, PoolSet, Pooled},
    row_buffer::{RowBuffer, TaggedRowBuffer},
    table_spec::{ColumnId, Generation, Offset, TableVersion, WrappedTable},
    OffsetRange,
};

#[cfg(test)]
mod tests;
struct TableEntry<T> {
    hash: u64,
    /// Points into `keys`
    key: RowId,
    vals: T,
}

pub(crate) struct Index<TI> {
    key: Vec<ColumnId>,
    updated_to: TableVersion,
    table: TI,
}

impl<TI: IndexBase> Index<TI> {
    pub(crate) fn new(key: Vec<ColumnId>, table: TI) -> Self {
        Index {
            key,
            updated_to: TableVersion {
                major: Generation::new(0),
                minor: Offset::new(0),
            },
            table,
        }
    }

    /// Get the nonempty subset of rows associated with this key, if there is
    /// one.
    pub(crate) fn get_subset(&self, key: &TI::Key) -> Option<SubsetRef> {
        self.table.get_subset(key)
    }

    /// Update the contents of the index to the current version of the table.
    ///
    /// The index is guaranteed to be up to date until `merge` is called on the
    /// table again.
    pub(crate) fn refresh(&mut self, table: &WrappedTable, pool_set: &PoolSet) {
        let cur_version = table.version();
        if cur_version == self.updated_to {
            return;
        }
        let subset = if cur_version.major != self.updated_to.major {
            self.table.clear();
            table.all(pool_set)
        } else {
            table.updates_since(self.updated_to.minor, pool_set)
        };
        let mut buf = TaggedRowBuffer::new(self.key.len(), pool_set);
        let mut cur = Offset::new(0);
        loop {
            buf.clear();
            if let Some(next) =
                table.scan_project(subset.as_ref(), &self.key, cur, 1024, &[], &mut buf)
            {
                cur = next;
                self.table.merge_rows(&buf, pool_set);
            } else {
                self.table.merge_rows(&buf, pool_set);
                break;
            }
        }
        self.updated_to = cur_version;
    }

    pub(crate) fn for_each(&self, f: impl FnMut(&TI::Key, SubsetRef)) {
        self.table.for_each(f);
    }

    pub(crate) fn len(&self) -> usize {
        self.table.len()
    }
}

// Define a newtype to hook things into the PoolSet machinery.
#[derive(Default)]
pub(crate) struct SubsetTable(RawTable<TableEntry<BufferedSubset>>);

impl Clear for SubsetTable {
    fn clear(&mut self) {
        self.0.clear();
    }
    fn reuse(&self) -> bool {
        self.0.capacity() > 0
    }
}

// Define a newtype to hook things into the PoolSet machinery.
#[derive(Default)]
pub(crate) struct KeyPresenceTable(RawTable<TableEntry<()>>);

impl Clear for KeyPresenceTable {
    fn clear(&mut self) {
        self.0.clear();
    }
    fn reuse(&self) -> bool {
        self.0.capacity() > 0
    }
}

pub(crate) trait IndexBase {
    /// The type of keys for this index.  Keys can have validity constraints
    /// (e.g. the arity of a slice for `Key = [Value]`). If keys are invalid,
    /// these methods can panic.
    type Key: ?Sized;
    /// Remove any existing entries in the index.
    fn clear(&mut self);
    /// Get the subset corresponding to this key, if there is one.
    fn get_subset<'a>(&'a self, key: &Self::Key) -> Option<SubsetRef<'a>>;
    /// Add the given key and row id to the table.
    fn add_row(&mut self, key: &Self::Key, row: RowId, ps: &PoolSet);
    /// Merge the contents of the [`TaggedRowBuffer`] into the table.
    fn merge_rows(&mut self, buf: &TaggedRowBuffer, pool_set: &PoolSet);
    /// Call `f` over the elements of the index.
    fn for_each(&self, f: impl FnMut(&Self::Key, SubsetRef));
    /// The number of keys in the index.
    fn len(&self) -> usize;
}

pub struct ColumnIndex {
    // A specialized index used when we are indexing on a single column.
    table: Pooled<IndexMap<Value, BufferedSubset>>,
    subsets: SubsetBuffer,
}

impl IndexBase for ColumnIndex {
    type Key = Value;
    fn clear(&mut self) {
        self.table.clear();
    }
    fn get_subset(&self, key: &Value) -> Option<SubsetRef> {
        self.table.get(key).map(|x| x.as_ref(&self.subsets))
    }
    fn add_row(&mut self, key: &Value, row: RowId, _: &PoolSet) {
        self.table
            .entry(*key)
            .or_insert_with(BufferedSubset::empty)
            .add_row_sorted(row, &mut self.subsets);
    }
    fn merge_rows(&mut self, buf: &TaggedRowBuffer, pool_set: &PoolSet) {
        for (src_id, key) in buf.iter() {
            debug_assert_eq!(key.len(), 1);
            self.add_row(&key[0], src_id, pool_set);
        }
    }
    fn for_each(&self, mut f: impl FnMut(&Self::Key, SubsetRef)) {
        for (k, v) in self.table.iter() {
            f(k, v.as_ref(&self.subsets));
        }
    }
    fn len(&self) -> usize {
        self.table.len()
    }
}

impl ColumnIndex {
    pub(crate) fn new(pool_set: &PoolSet) -> ColumnIndex {
        ColumnIndex {
            table: pool_set.get(),
            subsets: SubsetBuffer::new(pool_set),
        }
    }
}

/// A mapping from keys to subsets of rows.
pub struct TupleIndex {
    // NB: we could store RowBuffers inline and then have indexes reference
    // (u32, RowId) instead of RowId. Trades copying off for indirections.
    subsets: SubsetBuffer,
    keys: RowBuffer,
    table: Pooled<SubsetTable>,
}

impl TupleIndex {
    pub(crate) fn new(key_arity: usize, pool_set: &PoolSet) -> TupleIndex {
        let keys = RowBuffer::new(key_arity, pool_set);
        let table = pool_set.get();
        TupleIndex {
            keys,
            table,
            subsets: SubsetBuffer::new(pool_set),
        }
    }
}

impl IndexBase for TupleIndex {
    type Key = [Value];

    fn clear(&mut self) {
        self.keys.clear();
        self.table.clear();
    }

    fn get_subset(&self, key: &[Value]) -> Option<SubsetRef> {
        let hash = hash_key(key);
        let entry = self.table.0.get(hash, |entry| {
            entry.hash == hash && self.keys.get_row(entry.key) == key
        })?;
        Some(entry.vals.as_ref(&self.subsets))
    }

    fn add_row(&mut self, key: &[Value], row: RowId, _: &PoolSet) {
        let hash = hash_key(key);
        if let Some(entry) = self.table.0.get_mut(hash, |entry| {
            entry.hash == hash && self.keys.get_row(entry.key) == key
        }) {
            entry.vals.add_row_sorted(row, &mut self.subsets);
        } else {
            let key_id = self.keys.add_row(key);
            let subset = BufferedSubset::singleton(row);
            self.table.0.insert(
                hash,
                TableEntry {
                    hash,
                    key: key_id,
                    vals: subset,
                },
                |entry| entry.hash,
            );
        }
    }

    fn merge_rows(&mut self, buf: &TaggedRowBuffer, pool_set: &PoolSet) {
        for (src_id, key) in buf.iter() {
            self.add_row(key, src_id, pool_set);
        }
    }
    fn for_each(&self, mut f: impl FnMut(&Self::Key, SubsetRef)) {
        // SAFETY: `f` cannot leak references from the callback due to its type.
        for entry in unsafe { self.table.0.iter() } {
            let entry = unsafe { entry.as_ref() };
            let key = self.keys.get_row(entry.key);
            f(key, entry.vals.as_ref(&self.subsets));
        }
    }

    fn len(&self) -> usize {
        self.table.0.len()
    }
}

fn hash_key(key: &[Value]) -> u64 {
    let mut hasher = FxHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

define_id!(BufferIndex, u32, "an index into a subset buffer");

/// A shared pool of row ids used to store sorted offset vectors with a common
/// lifetime.
///
/// This is used as the backing store for subsets stored in indexes. While
/// definitely saves some allocations, the primary use for SubsetBuffer is to
/// make deallocation faster: with a standard [`crate::offsets::Subset`]
/// structure stored in the index, dropping requires an O(n) traversal of the
/// index. SubsetBuffer allows deallocation to happen in constant time (given
/// our use of memory pools).
struct SubsetBuffer {
    buf: Pooled<Vec<RowId>>,
    free_list: Vec<Vec<BufferIndex>>,
}

impl SubsetBuffer {
    fn new(ps: &PoolSet) -> Self {
        SubsetBuffer {
            buf: ps.get(),
            free_list: Vec::new(),
        }
    }

    fn new_vec(&mut self, rows: impl ExactSizeIterator<Item = RowId>) -> BufferedVec {
        let len = rows.len();
        assert!(len > 0);
        let size_class = len.next_power_of_two().trailing_zeros() as usize;
        if let Some(v) = self.free_list.get_mut(size_class).and_then(Vec::pop) {
            return self.fill_at(v, rows);
        }
        let start = BufferIndex::from_usize(self.buf.len());
        self.buf.resize(
            start.index() + len.next_power_of_two(),
            RowId::new(u32::MAX),
        );
        self.fill_at(start, rows)
    }

    fn fill_at(
        &mut self,
        start: BufferIndex,
        rows: impl ExactSizeIterator<Item = RowId>,
    ) -> BufferedVec {
        let mut cur = start;
        for i in rows {
            self.buf[cur.index()] = i;
            cur = cur.inc();
        }
        BufferedVec(start, cur)
    }

    fn push_vec(&mut self, vec: BufferedVec, row: RowId) -> BufferedVec {
        assert!(
            vec.is_empty() || self.buf[vec.1.index() - 1] <= row,
            "vec={vec:?}, row={row:?}, last_elt={:?}",
            self.buf[vec.1.index() - 1]
        );
        if !vec.len().is_power_of_two() {
            self.buf[vec.1.index()] = row;
            return BufferedVec(vec.0, vec.1.inc());
        }
        // The vector is full.  Add it to the free list.
        let size_class = vec.len().trailing_zeros() as usize;
        if self.free_list.len() <= size_class {
            self.free_list.resize_with(size_class + 1, Vec::new);
        }

        // Allocate a new one and move the contents over.
        self.free_list[size_class].push(vec.0);
        let next = size_class + 1;
        if let Some(v) = self.free_list.get_mut(next).and_then(Vec::pop) {
            self.buf
                .copy_within(vec.0.index()..vec.1.index(), v.index());
            self.buf[v.index() + vec.len()] = row;
            BufferedVec(v, BufferIndex::from_usize(v.index() + vec.len() + 1))
        } else {
            let start = self.buf.len();
            self.buf.resize(
                start + (vec.len() + 1).next_power_of_two(),
                RowId::new(u32::MAX),
            );
            self.buf.copy_within(vec.0.index()..vec.1.index(), start);
            self.buf[start + vec.len()] = row;
            let end = start + vec.len() + 1;
            BufferedVec(BufferIndex::from_usize(start), BufferIndex::from_usize(end))
        }
    }

    fn make_ref<'a>(&'a self, vec: &BufferedVec) -> SubsetRef<'a> {
        // SAFETY: if `vec` is a valid index into self.buf, it will be sorted.
        //
        // NB: we do not guarantee this in the type signature of BufferedVec,
        // etc. But this is indeed safe given the usage within this module.
        let res = SubsetRef::Sparse(unsafe {
            SortedOffsetSlice::new_unchecked(&self.buf[vec.0.index()..vec.1.index()])
        });
        #[cfg(debug_assertions)]
        {
            use crate::offsets::Offsets;
            res.offsets(|x| assert_ne!(x.rep(), u32::MAX))
        }
        res
    }
}

/// A sorted vector of offsets stored in a [`SubsetBuffer`].
#[derive(Debug)]
pub(crate) struct BufferedVec(BufferIndex, BufferIndex);

impl Default for BufferedVec {
    fn default() -> Self {
        BufferedVec(BufferIndex::new(0), BufferIndex::new(0))
    }
}

impl BufferedVec {
    fn is_empty(&self) -> bool {
        self.0 == self.1
    }
    fn len(&self) -> usize {
        self.1.index() - self.0.index()
    }
}

pub(crate) enum BufferedSubset {
    Dense(OffsetRange),
    Sparse(BufferedVec),
}

impl BufferedSubset {
    fn add_row_sorted(&mut self, row: RowId, buf: &mut SubsetBuffer) {
        match self {
            BufferedSubset::Dense(range) => {
                if range.end == range.start {
                    range.start = row;
                    range.end = row.inc();
                    return;
                }
                if range.end == row {
                    range.end = row.inc();
                    return;
                }
                let mut v = buf.new_vec((range.start.rep()..range.end.rep()).map(RowId::new));
                v = buf.push_vec(v, row);
                *self = BufferedSubset::Sparse(v);
            }
            BufferedSubset::Sparse(vec) => {
                *vec = buf.push_vec(mem::take(vec), row);
            }
        }
    }

    fn empty() -> Self {
        BufferedSubset::Dense(OffsetRange::new(RowId::new(0), RowId::new(0)))
    }

    fn singleton(row: RowId) -> Self {
        BufferedSubset::Dense(OffsetRange::new(row, row.inc()))
    }

    fn as_ref<'a>(&self, buf: &'a SubsetBuffer) -> SubsetRef<'a> {
        match self {
            BufferedSubset::Dense(range) => SubsetRef::Dense(*range),
            BufferedSubset::Sparse(vec) => buf.make_ref(vec),
        }
    }
}

//! Indexes on specific projections of tables.
use std::hash::{Hash, Hasher};

use hashbrown::raw::RawTable;
use rustc_hash::FxHasher;

use crate::{
    common::Value,
    offsets::{RowId, Subset},
    pool::{Clear, PoolSet, Pooled},
    row_buffer::{RowBuffer, TaggedRowBuffer},
    table_spec::{ColumnId, Generation, Offset, Table, TableVersion},
};

#[cfg(test)]
mod tests;
struct TableEntry<T> {
    hash: u64,
    /// Points into `keys`
    key: RowId,
    vals: T,
}

pub(crate) struct Index {
    key: Vec<ColumnId>,
    updated_to: TableVersion,
    pivot: PivotTable,
}

impl Index {
    pub(crate) fn new(key: Vec<ColumnId>, pool_set: &PoolSet) -> Index {
        let arity = key.len();
        Index {
            key,
            updated_to: TableVersion {
                major: Generation::new(0),
                minor: Offset::new(0),
            },
            pivot: PivotTable::new(arity, pool_set),
        }
    }

    /// Get the nonempty subset of rows associated with this key, if there is
    /// one.
    pub(crate) fn get_subset(&self, key: &[Value]) -> Option<&Subset> {
        self.pivot.get_subset(key)
    }

    /// Update the contents of the index to the current version of the table.
    ///
    /// The index is guaranteed to be up to date until `merge` is called on the
    /// table again.
    pub(crate) fn refresh(&mut self, table: &dyn Table, pool_set: &PoolSet) {
        let cur_version = table.version();
        if cur_version == self.updated_to {
            return;
        }
        let subset = if cur_version.major != self.updated_to.major {
            self.pivot.clear();
            table.all(pool_set)
        } else {
            table.updates_since(self.updated_to.minor, pool_set)
        };
        let mut buf = TaggedRowBuffer::new(self.key.len(), pool_set);
        let mut cur = Offset::new(0);
        loop {
            buf.clear();
            if let Some(next) = table.scan_project(&subset, &self.key, cur, 1024, &[], &mut buf) {
                cur = next;
                self.pivot.merge_rows(&buf, pool_set);
            } else {
                self.pivot.merge_rows(&buf, pool_set);
                break;
            }
        }
        self.updated_to = cur_version;
    }
}

// Define a newtype to hook things into the PoolSet machinery.
#[derive(Default)]
pub(crate) struct SubsetTable(RawTable<TableEntry<Subset>>);

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

pub(crate) struct KeySet {
    keys: RowBuffer,
    table: Pooled<KeyPresenceTable>,
}

impl KeySet {
    pub(crate) fn new(key_arity: usize, pool_set: &PoolSet) -> KeySet {
        let keys = RowBuffer::new(key_arity, pool_set);
        let table = pool_set.get();
        KeySet { keys, table }
    }

    pub(crate) fn insert(&mut self, key: &[Value]) -> bool {
        let hash = hash_key(key);
        if self
            .table
            .0
            .get_mut(hash, |entry| {
                entry.hash == hash && self.keys.get_row(entry.key) == key
            })
            .is_some()
        {
            false
        } else {
            let key_id = self.keys.add_row(key);
            self.table.0.insert(
                hash,
                TableEntry {
                    hash,
                    key: key_id,
                    vals: (),
                },
                |entry| entry.hash,
            );
            true
        }
    }
}

/// A mapping from keys to subsets of rows.
pub struct PivotTable {
    // NB: we could store RowBuffers inline and then have indexes reference
    // (u32, RowId) instead of RowId. Trades copying off for indirections.
    keys: RowBuffer,
    table: Pooled<SubsetTable>,
}

impl PivotTable {
    pub(crate) fn new(key_arity: usize, pool_set: &PoolSet) -> PivotTable {
        let keys = RowBuffer::new(key_arity, pool_set);
        let table = pool_set.get();
        PivotTable { keys, table }
    }

    /// Clear the contents of the table.
    ///
    /// Future insertions to the table must have the same arity as the key
    /// passed to the table.
    pub(crate) fn clear(&mut self) {
        self.keys.clear();
        self.table.clear();
    }

    /// Get the nonempty subset of rows associated with this key, if there is
    /// one.
    pub(crate) fn get_subset(&self, key: &[Value]) -> Option<&Subset> {
        let hash = hash_key(key);
        let entry = self.table.0.get(hash, |entry| {
            entry.hash == hash && self.keys.get_row(entry.key) == key
        })?;
        Some(&entry.vals)
    }

    /// Add the given key and row id to the table.
    ///
    /// # Panics
    /// The rows contained in this buffer must be greater than any existing rows
    /// for the given key.
    ///
    /// This method also panics if `key` has the wrong arity.
    pub(crate) fn add_row(&mut self, key: &[Value], row: RowId, ps: &PoolSet) {
        let hash = hash_key(key);
        if let Some(entry) = self.table.0.get_mut(hash, |entry| {
            entry.hash == hash && self.keys.get_row(entry.key) == key
        }) {
            entry.vals.add_row_sorted(row, ps);
        } else {
            let key_id = self.keys.add_row(key);
            let mut subset = Subset::empty();
            subset.add_row_sorted(row, ps);
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

    /// Merge the contents of the [`TaggedRowBuffer`] into the table.
    ///
    /// # Panics
    /// The rows contained in this buffer must be greater than any existing rows
    /// for overlapping keys. This includes rows _within_ the buffer: though all
    /// tables implement this property today.
    ///
    /// This method also panics if `buf` contains rows with the wrong arity.
    pub(crate) fn merge_rows(&mut self, buf: &TaggedRowBuffer, pool_set: &PoolSet) {
        for (src_id, key) in buf.iter() {
            self.add_row(key, src_id, pool_set);
        }
    }
}

fn hash_key(key: &[Value]) -> u64 {
    let mut hasher = FxHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

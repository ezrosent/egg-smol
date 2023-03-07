//! A simple associative caching scheme for operations on a ZDD.
//!
//! Knuth describes this strategy in TAOCP 4A in the section on BDDs.

use std::hash::{Hash, Hasher};

use rustc_hash::FxHasher;

pub(crate) struct Cache<K, V> {
    table: Vec<Option<(K, V)>>,
}

impl<K: Hash + Eq, V> Cache<K, V> {
    pub(crate) fn new(cap: usize) -> Cache<K, V> {
        let mut table = Vec::new();
        table.resize_with(cap.next_power_of_two(), || None);
        Cache { table }
    }
    fn get_index(&self, k: &K) -> usize {
        let mut hasher = FxHasher::default();
        k.hash(&mut hasher);
        (hasher.finish() as usize) & (self.table.len() - 1)
    }
    pub(crate) fn get(&self, k: &K) -> Option<&V> {
        let (candidate, v) = self.table[self.get_index(k)].as_ref()?;
        if k == candidate {
            Some(v)
        } else {
            None
        }
    }
    pub(crate) fn set(&mut self, k: K, v: V) {
        let ix = self.get_index(&k);
        self.table[ix] = Some((k, v))
    }
}

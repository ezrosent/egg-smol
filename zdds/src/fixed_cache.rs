//! A simple associative caching scheme for operations on a ZDD.
//!
//! Knuth describes this strategy in TAOCP 4A in the section on BDDs.

use std::{
    cmp,
    hash::{Hash, Hasher},
    mem,
};

use rustc_hash::FxHasher;

pub(crate) struct Cache<K, V> {
    max_size: usize,
    populated: usize,
    hits: usize,
    misses: usize,
    table: Vec<Option<(K, V)>>,
}

impl<K: Hash + Eq, V> Cache<K, V> {
    /// Create a new cache with size bounded by `cap`.
    pub(crate) fn new(cap: usize) -> Cache<K, V> {
        let mut table = Vec::new();
        let cap = cap.next_power_of_two();
        table.resize_with(cmp::min(128, cap), || None);
        Cache {
            max_size: cap,
            populated: 0,
            hits: 0,
            misses: 0,
            table,
        }
    }

    fn get_index(&self, k: &K) -> usize {
        let mut hasher = FxHasher::default();
        k.hash(&mut hasher);
        (hasher.finish() as usize) & (self.table.len() - 1)
    }

    fn should_grow(&self) -> bool {
        self.max_size > self.table.len() && ((self.table.len() * 3) / 4) <= self.populated
    }

    fn maybe_grow(&mut self) {
        if !self.should_grow() {
            return;
        }
        let mut new_vec = Vec::new();
        new_vec.resize_with(self.table.len() * 2, || None);
        mem::swap(&mut new_vec, &mut self.table);
        self.populated = 0;
        for (k, v) in new_vec.into_iter().flatten() {
            self.set(k, v);
        }
    }

    /// Get a cached value, if one is present.
    pub(crate) fn get(&mut self, k: &K) -> Option<&V> {
        let (candidate, v) = if let Some(x) = self.table[self.get_index(k)].as_ref() {
            x
        } else {
            self.misses += 1;
            return None;
        };
        if k == candidate {
            self.hits += 1;
            Some(v)
        } else {
            self.misses += 1;
            None
        }
    }

    /// Map `k` to `v` in the cache.
    pub(crate) fn set(&mut self, k: K, v: V) {
        let ix = self.get_index(&k);
        let slot = &mut self.table[ix];
        self.populated += usize::from(slot.is_none());
        *slot = Some((k, v));
        self.maybe_grow();
    }
}

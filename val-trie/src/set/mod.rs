//! Hash sets optimized to represent values in egglog.
use std::{
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use crate::node::{hash_value, Chunk, HashItem};

#[cfg(test)]
mod tests;

/// A persistent set data-structure.
#[derive(Debug, Clone)]
pub struct HashSet<T> {
    len: usize,
    node: Rc<Chunk<Inline<T>>>,
}

impl<T> Default for HashSet<T> {
    fn default() -> Self {
        HashSet {
            len: 0,
            node: Default::default(),
        }
    }
}

impl<T: Hash + Eq + Clone> HashSet<T> {
    /// Apply `f` to each of the elements in the set. The order is unspecified.
    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        self.node.for_each(&mut |x| f(&x.0))
    }

    /// The number of elements in the set.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether or not the set is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether or not the set contains `t`.
    pub fn contains(&self, t: &T) -> bool {
        let hash = hash_value(t);
        self.node.get(t, hash, 0).is_some()
    }

    /// Insert `t` into the set. Returns whether or not a new element was inserted.
    pub fn insert(&mut self, t: T) -> bool {
        let hash = hash_value(&t);
        let res = Rc::make_mut(&mut self.node)
            .insert(Inline(t), hash, 0)
            .is_none();
        self.len += res as usize;
        res
    }

    /// Remove `t` from the set, if it is there. Returns whether or not `t` was
    /// present.
    pub fn remove(&mut self, t: &T) -> bool {
        let hash = hash_value(&t);
        let res = Rc::make_mut(&mut self.node).remove(t, hash, 0).is_some();
        self.len -= res as usize;
        res
    }
}

impl<T: PartialEq> PartialEq for HashSet<T> {
    fn eq(&self, other: &HashSet<T>) -> bool {
        self.len == other.len && (Rc::ptr_eq(&self.node, &other.node) || self.node == other.node)
    }
}

impl<T: Eq> Eq for HashSet<T> {}

impl<T> Hash for HashSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.node.hash(state)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct Inline<T>(T);

impl<T: fmt::Debug> fmt::Debug for Inline<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Hash + Eq + Clone> HashItem for Inline<T> {
    type Key = T;
    fn key(&self) -> &T {
        &self.0
    }
}

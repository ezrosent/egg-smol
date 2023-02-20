//! A persistent integer set optimized for efficient comparison and hashing.
use std::{
    hash::{BuildHasher, Hash, Hasher},
    rc::Rc,
};

use crate::node::{merge_leaves, Child, Item, Node};

#[cfg(test)]
mod tests;

/// A set of 64-bit integers.
#[derive(Debug, Clone)]
pub struct IntSet<State> {
    len: usize,
    state: State,
    data: Child<u64>,
}

impl<State: BuildHasher> IntSet<State> {
    /// Construct a set with a given hasher.
    ///
    /// Note that two equal sets constructed with different hashers are not
    /// guaranteed to compare as equal.
    pub fn with_hasher(state: State) -> IntSet<State> {
        IntSet {
            len: 0,
            state,
            data: Default::default(),
        }
    }

    /// Call `f` on each element of the set, in sorted order.
    pub fn for_each(&self, mut f: impl FnMut(u64)) {
        self.data.for_each(&mut |x| f(*x))
    }

    /// The current size of the set.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether or not the set is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Test whether `k` is present in the set.
    pub fn contains(&self, k: u64) -> bool {
        match &self.data {
            Child::Inner(n) => n.lookup(k.key(), 0) == Some(&k),
            Child::Leaf(l) => k == *l,
            Child::Null => false,
        }
    }

    /// Insert `k` into the set, return true if `k` was not previously in the
    /// set.
    pub fn insert(&mut self, k: u64) -> bool {
        let res = match &mut self.data {
            Child::Inner(n) => {
                let mut inserted = true;
                n.insert(k.key(), 0, &self.state, &mut |prev| {
                    inserted = prev.is_none();
                    k
                });
                inserted
            }
            Child::Leaf(l) => {
                if *l == k {
                    false
                } else {
                    let mut node = Node::default();
                    merge_leaves(*l, k, 0, &mut node, &mut self.state.build_hasher());
                    self.data = Child::Inner(Rc::new(node));
                    true
                }
            }
            Child::Null => {
                self.data = Child::Leaf(k);
                true
            }
        };

        if res {
            self.len += 1;
        }

        res
    }

    /// Remove `k` from the set, return true if `k` was not previously in the set.
    pub fn remove(&mut self, k: u64) -> bool {
        let res = self
            .data
            .mutate(k.key(), 0, &self.state, &mut |x| *x == k)
            .is_some();
        if res {
            self.len -= 1;
        }
        res
    }
}

impl Item for u64 {
    fn key(&self) -> u64 {
        *self
    }
}

impl<State> PartialEq for IntSet<State> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.data == other.data
    }
}

impl<State> Eq for IntSet<State> {}

impl<State> Hash for IntSet<State> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.data.hash(state);
    }
}

impl<State: BuildHasher + Default> Default for IntSet<State> {
    fn default() -> Self {
        IntSet {
            len: Default::default(),
            state: Default::default(),
            data: Default::default(),
        }
    }
}

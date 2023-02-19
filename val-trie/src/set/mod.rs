//! A persistent integer set optimized for efficient comparison and hashing.
use std::{
    hash::{BuildHasher, Hash, Hasher},
    rc::Rc,
};

use crate::node::{merge_leaves, Child, Item, Node};

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct IntSet<State> {
    len: usize,
    state: State,
    data: Child<u64>,
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

impl<State: BuildHasher> IntSet<State> {
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

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
            .mutate(k.key(), 0, &self.state, &mut |_| true)
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

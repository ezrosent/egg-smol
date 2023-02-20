//! A persistent map with integer keys optimized for efficient comparison and
//! hashing.

use std::{
    hash::{BuildHasher, Hash, Hasher},
    mem,
    rc::Rc,
};

use crate::node::{merge_leaves, Child, Item};

#[cfg(test)]
mod tests;

/// A map from 64-bit integers to values.
#[derive(Debug, Clone)]
pub struct IntMap<V, State> {
    len: usize,
    state: State,
    data: Child<(u64, V)>,
}

impl<V: Clone, State: BuildHasher> IntMap<V, State> {
    /// Construct a set with a given hasher.
    ///
    /// Note that two equal sets constructed with different hashers are not
    /// guaranteed to compare as equal.
    pub fn with_hasher(state: State) -> IntMap<V, State> {
        IntMap {
            len: 0,
            state,
            data: Default::default(),
        }
    }

    /// Call `f` on each element of the map, in sorted order.
    pub fn for_each(&self, mut f: impl FnMut(u64, &V)) {
        self.data.for_each(&mut |(k, v)| f(*k, v))
    }

    /// The current size of the map.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether or not the map is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Test whether `k` is present in the map.
    pub fn contains_key(&self, k: u64) -> bool {
        self.get(k).is_some()
    }

    /// Get the value corresponding to `k` if it is present in the map.
    pub fn get(&self, k: u64) -> Option<&V> {
        match &self.data {
            Child::Inner(n) => {
                let (key, v) = n.lookup(k, 0)?;
                if *key == k {
                    Some(v)
                } else {
                    None
                }
            }
            Child::Leaf((key, v)) => {
                if *key == k {
                    Some(v)
                } else {
                    None
                }
            }
            Child::Null => None,
        }
    }

    /// Insert `k` into the map, mapped to `v`, returning the old value if it
    /// was present.
    pub fn insert(&mut self, k: u64, mut v: V) -> Option<V> {
        let mut prev = None;
        match &mut self.data {
            Child::Inner(n) => {
                let prev_ref = &mut prev;
                n.insert(k, 0, &self.state, move |was: Option<&(u64, V)>| {
                    if let Some((_k, prev_val)) = was {
                        debug_assert_eq!(k, *_k);
                        *prev_ref = Some(prev_val.clone());
                    }
                    (k, v)
                });
            }
            Child::Leaf((key, val)) => {
                if *key == k {
                    mem::swap(&mut v, val);
                    prev = Some(v);
                } else {
                    // To avoid cloning 'v', do a couple swaps.
                    let leaf = mem::replace(&mut self.data, Child::Inner(Default::default()));
                    let (key, val) = if let Child::Leaf(x) = leaf {
                        x
                    } else {
                        unreachable!()
                    };
                    let node = if let Child::Inner(n) = &mut self.data {
                        Rc::make_mut(n)
                    } else {
                        unreachable!()
                    };
                    merge_leaves((key, val), (k, v), 0, node, &mut self.state.build_hasher());
                }
            }
            x @ Child::Null => *x = Child::Leaf((k, v)),
        }
        if prev.is_none() {
            self.len += 1;
        }
        prev
    }

    /// Remove `k` from the set, return true if `k` was not previously in the
    /// set.
    pub fn remove(&mut self, k: u64) -> Option<V> {
        let (_, v) = self
            .data
            .mutate(k, 0, &self.state, &mut |(key, _)| k == *key)?;
        self.len -= 1;
        Some(v)
    }
}

impl<V: Clone> Item for (u64, V) {
    fn key(&self) -> u64 {
        self.0
    }
}

impl<V, State: BuildHasher + Default> Default for IntMap<V, State> {
    fn default() -> Self {
        IntMap {
            len: Default::default(),
            state: Default::default(),
            data: Default::default(),
        }
    }
}

impl<V: Clone + PartialEq, State> PartialEq for IntMap<V, State> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.data == other.data
    }
}

impl<V: Clone + Eq, State> Eq for IntMap<V, State> {}

impl<V: Hash + Clone, State> Hash for IntMap<V, State> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.data.hash(state);
    }
}

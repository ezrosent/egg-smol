use std::{
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use crate::hash_node::{hash_value, Chunk, HashItem};

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
    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        self.node.for_each(&mut |x| f(&x.0))
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn contains(&self, t: &T) -> bool {
        let hash = hash_value(t);
        self.node.get(t, hash, 0).is_some()
    }

    pub fn insert(&mut self, t: T) -> bool {
        let hash = hash_value(&t);
        let res = Rc::make_mut(&mut self.node)
            .insert(Inline(t), hash, 0)
            .is_none();
        self.len += res as usize;
        res
    }

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

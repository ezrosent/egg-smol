use core::fmt;
use std::{
    hash::{Hash, Hasher},
    rc::Rc,
};

use super::chunk::Chunk;

#[derive(Clone, Default)]
pub struct IntSet {
    len: usize,
    data: Rc<Chunk<u64>>,
}

impl fmt::Debug for IntSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IntSet{{len={}, ...}}", self.len)
    }
}

// TODO roll back the unsafe bits!

impl IntSet {
    pub fn contains(&self, k: u64) -> bool {
        self.data.contains_key(k, 0)
        // self.data.get(k, 0) == Some(&k)
    }

    /// The current size of the set.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether or not the set is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Insert `k` into the set, return true if `k` was not previously in the
    /// set.
    pub fn insert(&mut self, k: u64) -> bool {
        let inserted = Rc::make_mut(&mut self.data).insert(k, 0, k).is_none();
        if inserted {
            self.len += 1;
        }
        inserted
    }

    // TODO: consistent use of `k` vs. `key`

    pub fn remove(&mut self, key: u64) -> bool {
        if Rc::make_mut(&mut self.data)
            .remove(key, 0, |x| *x == key)
            .is_some()
        {
            self.len -= 1;
            true
        } else {
            false
        }
    }
    pub fn for_each(&mut self, mut f: impl FnMut(u64)) {
        self.data.for_each(&mut |x| f(*x))
    }
}

impl PartialEq for IntSet {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && (Rc::ptr_eq(&self.data, &other.data) || self.data == other.data)
    }
}

impl Eq for IntSet {}

impl Hash for IntSet {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.data.hash(state);
    }
}

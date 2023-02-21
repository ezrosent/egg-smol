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

impl IntSet {
    pub fn contains(&self, k: u64) -> bool {
        self.data.get(k, 0) == Some(&k)
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

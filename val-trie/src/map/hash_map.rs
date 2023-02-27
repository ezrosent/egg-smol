use std::{
    hash::{Hash, Hasher},
    rc::Rc,
};

use crate::hash_node::{hash_value, Chunk, HashItem};

#[derive(Debug)]
pub struct HashMap<K, V> {
    len: usize,
    node: Rc<Chunk<Pair<K, V>>>,
}

impl<K: Hash + Eq + Clone, V: Clone> HashMap<K, V> {
    pub fn for_each(&self, mut f: impl FnMut(&K, &V)) {
        self.node.for_each(&mut |pair| f(pair.key(), pair.value()))
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        let hash = hash_value(k);
        Some(self.node.get(k, hash, 0)?.value())
    }

    pub fn contains_key(&self, k: &K) -> bool {
        let hash = hash_value(k);
        self.node.get(k, hash, 0).is_some()
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let hash = hash_value(&k);
        let res = Rc::make_mut(&mut self.node).insert(Pair(k, v), hash, 0);
        if let Some(prev) = res {
            Some(prev.1)
        } else {
            self.len += 1;
            None
        }
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        let hash = hash_value(k);
        let res = Rc::make_mut(&mut self.node).remove(k, hash, 0)?;
        self.len -= 1;
        Some(res.1)
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for HashMap<K, V> {
    fn eq(&self, other: &HashMap<K, V>) -> bool {
        self.len == other.len && (Rc::ptr_eq(&self.node, &other.node) || self.node == other.node)
    }
}

impl<K: Eq, V: Eq> Eq for HashMap<K, V> {}

impl<K, V> Hash for HashMap<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        self.node.hash(state);
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct Pair<K, V>(K, V);

impl<K, V> Pair<K, V> {
    fn value(&self) -> &V {
        &self.1
    }
}

impl<K: Hash + Eq + Clone, V: Clone> HashItem for Pair<K, V> {
    type Key = K;
    fn key(&self) -> &K {
        &self.0
    }
}

impl<K, V> Default for HashMap<K, V> {
    fn default() -> HashMap<K, V> {
        HashMap {
            len: 0,
            node: Default::default(),
        }
    }
}

impl<K, V> Clone for HashMap<K, V> {
    fn clone(&self) -> HashMap<K, V> {
        HashMap {
            len: self.len,
            node: self.node.clone(),
        }
    }
}

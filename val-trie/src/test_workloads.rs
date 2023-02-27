use std::{
    collections::{BTreeMap, BTreeSet},
    hash::{Hash, Hasher},
    iter::once,
};

use crate::{HashMap, HashSet};

#[derive(Debug)]
pub(crate) enum Operation {
    Insert(u64),
    Remove(u64),
    Dump,
}

pub(crate) fn test_hash_map(ops: impl IntoIterator<Item = Operation>) {
    let mut oracle = BTreeMap::<u64, u64>::new();
    let mut map1 = HashMap::default();
    let mut map2 = HashMap::default();
    for op in ops {
        match op {
            Operation::Insert(i) => {
                let k = i;
                let v = i + 1;
                assert_eq!(oracle.get(&k), map1.get(&k));
                assert_eq!(oracle.insert(k, v), map1.insert(k, v));
                map2.insert(k, v);
                assert_eq!(map1, map2);
                assert_eq!(oracle.get(&k), map1.get(&k));
                assert_eq!(oracle.contains_key(&k), map1.contains_key(&k));
                assert_eq!(oracle.len(), map1.len());
            }
            Operation::Remove(i) => {
                assert_eq!(oracle.contains_key(&i), map1.contains_key(&i));
                assert_eq!(oracle.remove(&i), map1.remove(&i));
                map2.remove(&i);
                assert_eq!(map1, map2);
                assert_eq!(oracle.contains_key(&i), map1.contains_key(&i));
                assert_eq!(oracle.len(), map1.len());
            }
            Operation::Dump => {
                assert_eq!(oracle.len(), map1.len());
                let v1: Vec<(u64, u64)> = oracle.iter().map(|(k, v)| (*k, *v)).collect();
                let mut v2: Vec<(u64, u64)> = Default::default();
                map1.for_each(|k, v| v2.push((*k, *v)));
                v2.sort();
                assert_eq!(v1, v2);
                for (k, _) in v1 {
                    assert_eq!(oracle.get(&k), map1.get(&k));
                }
            }
        }
    }
}

pub(crate) fn test_hash_map_collision(ops: impl IntoIterator<Item = Operation>) {
    let mut oracle = BTreeMap::<Collider, u64>::new();
    let mut map1 = HashMap::default();
    let mut map2 = HashMap::default();
    for op in ops {
        match op {
            Operation::Insert(i) => {
                let (k1, k2) = collider(i);
                let v = i + 1;
                assert_eq!(oracle.get(&k1), map1.get(&k1));
                assert_eq!(oracle.get(&k2), map1.get(&k2));
                assert_eq!(oracle.insert(k1, v), map1.insert(k1, v));
                assert_eq!(oracle.insert(k2, v), map1.insert(k2, v));
                map2.insert(k2, v);
                map2.insert(k1, v);
                assert_eq!(map1, map2);
                assert_eq!(oracle.get(&k1), map1.get(&k1));
                assert_eq!(oracle.get(&k2), map1.get(&k2));
                assert_eq!(oracle.contains_key(&k1), map1.contains_key(&k1));
                assert_eq!(oracle.contains_key(&k2), map1.contains_key(&k2));
                assert_eq!(oracle.len(), map1.len());
            }
            Operation::Remove(i) => {
                let (k1, k2) = collider(i);
                assert_eq!(oracle.contains_key(&k1), map1.contains_key(&k1));
                assert_eq!(oracle.contains_key(&k2), map1.contains_key(&k2));
                assert_eq!(oracle.remove(&k2), map1.remove(&k2));
                assert_eq!(oracle.remove(&k1), map1.remove(&k1));
                map2.remove(&k1);
                map2.remove(&k2);
                assert_eq!(map1, map2);
                assert_eq!(oracle.contains_key(&k2), map1.contains_key(&k2));
                assert_eq!(oracle.contains_key(&k1), map1.contains_key(&k1));
                assert_eq!(oracle.len(), map1.len());
            }
            Operation::Dump => {
                assert_eq!(oracle.len(), map1.len());
                let v1: Vec<(Collider, u64)> = oracle.iter().map(|(k, v)| (*k, *v)).collect();
                let mut v2: Vec<(Collider, u64)> = Default::default();
                map1.for_each(|k, v| v2.push((*k, *v)));
                v2.sort();
                assert_eq!(v1, v2);
                for (k, _) in v1 {
                    assert_eq!(oracle.get(&k), map1.get(&k));
                }
            }
        }
    }
}

pub(crate) fn test_hash_set(ops: impl IntoIterator<Item = Operation>) {
    let mut oracle = BTreeSet::<u64>::new();
    let mut set1 = HashSet::default();
    let mut set2 = HashSet::default();
    for op in ops {
        match op {
            Operation::Insert(i) => {
                assert_eq!(oracle.contains(&i), set1.contains(&i));
                assert_eq!(oracle.insert(i), set1.insert(i));
                set2.insert(i);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&i), set1.contains(&i));
                assert_eq!(oracle.len(), set1.len());
            }
            Operation::Remove(i) => {
                assert_eq!(oracle.contains(&i), set1.contains(&i));
                assert_eq!(oracle.remove(&i), set1.remove(&i));
                set2.remove(&i);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&i), set1.contains(&i));
                assert_eq!(oracle.len(), set1.len());
            }
            Operation::Dump => {
                assert_eq!(oracle.len(), set1.len());
                let v1: Vec<u64> = oracle.iter().copied().collect();
                let mut v2: Vec<u64> = Default::default();
                set1.for_each(|i| v2.push(*i));
                v2.sort();
                assert_eq!(v1, v2);
                for val in v1 {
                    assert_eq!(oracle.contains(&val), set1.contains(&val));
                }
            }
        }
    }
}

pub(crate) fn test_hash_set_collision(ops: impl IntoIterator<Item = Operation>) {
    let mut oracle = BTreeSet::<Collider>::new();
    let mut set1 = HashSet::default();
    let mut set2 = HashSet::default();

    for op in ops {
        match op {
            Operation::Insert(i) => {
                let (c1, c2) = collider(i);
                assert_eq!(oracle.contains(&c1), set1.contains(&c1));
                assert_eq!(oracle.contains(&c2), set1.contains(&c2));
                assert_eq!(oracle.insert(c1), set1.insert(c1));
                assert_eq!(oracle.insert(c2), set1.insert(c2));
                set2.insert(c2);
                set2.insert(c1);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&c1), set1.contains(&c1));
                assert_eq!(oracle.contains(&c2), set1.contains(&c2));
                assert_eq!(oracle.len(), set1.len());
            }
            Operation::Remove(i) => {
                let (c1, c2) = collider(i);
                assert_eq!(oracle.contains(&c1), set1.contains(&c1));
                assert_eq!(oracle.contains(&c2), set1.contains(&c2));
                assert_eq!(oracle.remove(&c1), set1.remove(&c1));
                assert_eq!(oracle.remove(&c2), set1.remove(&c2));
                set2.remove(&c1);
                set2.remove(&c2);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&c1), set1.contains(&c1));
                assert_eq!(oracle.contains(&c2), set1.contains(&c2));
                assert_eq!(oracle.len(), set1.len());
            }
            Operation::Dump => {
                assert_eq!(oracle.len(), set1.len());
                let v1: Vec<Collider> = oracle.iter().copied().collect();
                let mut v2: Vec<Collider> = Default::default();
                set1.for_each(|i| v2.push(*i));
                v2.sort();
                assert_eq!(v1, v2);
                for val in v1 {
                    assert_eq!(oracle.contains(&val), set1.contains(&val));
                }
            }
        }
    }
}

#[derive(Copy, Clone, Eq, PartialOrd, Ord, Debug)]
struct Collider(u64, u64);

impl Hash for Collider {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl PartialEq for Collider {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

fn collider(i: u64) -> (Collider, Collider) {
    (Collider(i, 0), Collider(i, 1))
}

pub(crate) fn insert_remove_sparse() -> impl Iterator<Item = Operation> {
    const N: usize = 1000;
    let to_insert: BTreeSet<u64> = (0..N).map(|_| rand::random::<u64>()).collect();
    let in_sequence: Vec<u64> = to_insert.into_iter().collect();
    let in_set: Vec<u64> = in_sequence[0..(N / 2)].to_vec();
    let not_in_set: Vec<u64> = in_sequence[(N / 2)..].to_vec();
    in_set
        .clone()
        .into_iter()
        .map(Operation::Insert)
        .chain(once(Operation::Dump))
        .chain(not_in_set.into_iter().map(Operation::Remove))
        .chain(once(Operation::Dump))
        .chain(in_set.into_iter().map(Operation::Remove))
        .chain(once(Operation::Dump))
}

pub(crate) fn insert_remove_dense() -> impl Iterator<Item = Operation> {
    (0..1000)
        .map(Operation::Insert)
        .chain(once(Operation::Dump))
        .chain((0..1000).map(Operation::Remove))
        .chain(once(Operation::Dump))
}

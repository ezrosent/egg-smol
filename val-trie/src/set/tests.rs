use std::{
    collections::{hash_map::RandomState, BTreeSet},
    iter::once,
};

use hashbrown::HashSet;

use crate::IntSet;

#[derive(Debug)]
enum Operation {
    Insert(u64),
    Remove(u64),
    Dump,
}

fn test_program(ops: impl IntoIterator<Item = Operation>) {
    let mut oracle = BTreeSet::<u64>::new();
    let state = RandomState::default();
    let mut set1 = IntSet::with_hasher(state.clone());
    let mut set2 = IntSet::with_hasher(state);
    for op in ops {
        match op {
            Operation::Insert(i) => {
                assert_eq!(oracle.insert(i), set1.insert(i));
                set2.insert(i);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&i), set1.contains(i));
            }
            Operation::Remove(i) => {
                assert_eq!(oracle.remove(&i), set1.remove(i));
                set2.remove(i);
                assert_eq!(set1, set2);
                assert_eq!(oracle.contains(&i), set1.contains(i));
            }
            Operation::Dump => {
                assert_eq!(oracle.len(), set1.len());
                let v1: Vec<u64> = oracle.iter().copied().collect();
                let mut v2: Vec<u64> = Default::default();
                set1.for_each(|i| v2.push(i));
                assert_eq!(v1, v2);
                for val in v1 {
                    assert_eq!(oracle.contains(&val), set1.contains(val));
                }
            }
        }
    }
}

#[test]
fn insert_remove_dense() {
    test_program(
        (0..1000)
            .map(Operation::Insert)
            .chain(once(Operation::Dump))
            .chain((0..1000).map(Operation::Remove))
            .chain(once(Operation::Dump)),
    )
}

#[test]
fn insert_remove_sparse() {
    const N: usize = 1000;
    let to_insert: HashSet<u64> = (0..N).map(|_| rand::random::<u64>()).collect();
    let in_sequence: Vec<u64> = to_insert.into_iter().collect();
    let in_set: Vec<u64> = in_sequence[0..(N / 2)].to_vec();
    let not_in_set: Vec<u64> = in_sequence[(N / 2)..].to_vec();
    test_program(
        in_set
            .iter()
            .copied()
            .map(Operation::Insert)
            .chain(once(Operation::Dump))
            .chain(not_in_set.iter().copied().map(Operation::Remove))
            .chain(once(Operation::Dump))
            .chain(in_set.iter().copied().map(Operation::Remove))
            .chain(once(Operation::Dump)),
    )
}

#[test]
fn basic_set() {
    let mut s = IntSet::<RandomState>::default();

    assert!(s.insert(1));
    assert!(s.insert(2));
    assert!(s.insert(3));

    assert!(s.contains(1));
    assert!(s.contains(2));
    assert!(s.contains(3));
    assert!(!s.contains(4));

    assert!(s.remove(2));
    assert!(!s.remove(2));

    assert!(s.contains(1));
    assert!(!s.contains(2));
    assert!(s.contains(3));
    assert!(!s.contains(4));

    assert!(s.insert(1024));
    assert!(s.contains(1));
    assert!(!s.contains(2));
    assert!(s.contains(3));
    assert!(!s.contains(4));
    assert!(s.contains(1024));

    assert!(s.insert(!2048 >> 5));
    assert!(s.contains(1));
    assert!(!s.contains(2));
    assert!(s.contains(3));
    assert!(!s.contains(4));
    assert!(s.contains(1024));
    assert!(s.contains(!2048 >> 5));

    eprintln!("set={:#?}", s.data);
}

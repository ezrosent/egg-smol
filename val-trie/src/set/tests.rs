use std::{collections::hash_map::RandomState, hash::BuildHasherDefault};

use crate::IntSet;

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

// TODO: oracles, iterators, etc.

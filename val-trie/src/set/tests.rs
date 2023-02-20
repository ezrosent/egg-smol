use std::collections::hash_map::RandomState;

use crate::{
    test_workloads::{self, test_set},
    IntSet,
};

#[test]
fn insert_remove_dense() {
    test_set(test_workloads::insert_remove_dense())
}

#[test]
fn insert_remove_sparse() {
    test_set(test_workloads::insert_remove_sparse())
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
}

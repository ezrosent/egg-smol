use crate::test_workloads::{self, test_hash_map};

#[test]
fn insert_remove_hash_dense() {
    test_hash_map(test_workloads::insert_remove_dense())
}

#[test]
fn insert_remove_hash_sparse() {
    test_hash_map(test_workloads::insert_remove_sparse())
}

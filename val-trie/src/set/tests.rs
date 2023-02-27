use crate::test_workloads::{self, test_hash_set, test_hash_set_collision};

#[test]
fn insert_remove_hash_dense() {
    test_hash_set(test_workloads::insert_remove_dense())
}

#[test]
fn insert_remove_hash_sparse() {
    test_hash_set(test_workloads::insert_remove_sparse())
}

#[test]
fn insert_remove_hash_dense_collisions() {
    test_hash_set_collision(test_workloads::insert_remove_dense())
}

#[test]
fn insert_remove_hash_sparse_collisions() {
    test_hash_set_collision(test_workloads::insert_remove_sparse())
}

use crate::test_workloads::{self, test_map};

#[test]
fn insert_remove_dense() {
    test_map(test_workloads::insert_remove_dense())
}

#[test]
fn insert_remove_sparse() {
    test_map(test_workloads::insert_remove_sparse())
}

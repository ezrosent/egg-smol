use crate::{define_id, uf::UpdateTrackingUnionFind};

use super::UnionFind;

#[test]
fn basic_uf() {
    let mut uf = UpdateTrackingUnionFind::<usize>::default();
    let a = uf.fresh();
    let b = uf.fresh();
    assert_ne!(a, b);
    assert_eq!(uf.find(a), a);
    assert!(uf.recent_reparents().is_empty());
    let (parent, child) = uf.union(a, b);
    assert_eq!(uf.find(a), uf.find(b));
    assert_eq!(uf.find(a), parent);
    assert!(uf.recent_reparents().is_empty());
    uf.advance();
    assert_eq!(
        Vec::from_iter(uf.recent_reparents().iter().copied()),
        vec![child]
    );
}

#[test]
fn larger_chain() {
    define_id!(UfId, u32);
    let mut uf = UnionFind::<UfId>::default();
    let ids1 = (0..100).map(|_| uf.fresh()).collect::<Vec<_>>();
    let ids2 = (0..100).map(|_| uf.fresh()).collect::<Vec<_>>();

    ids1.windows(2).for_each(|w| {
        uf.union(w[0], w[1]);
    });
    ids2.windows(2).for_each(|w| {
        uf.union(w[0], w[1]);
    });

    assert!(ids1.windows(2).all(|w| uf.find(w[0]) == uf.find(w[1])));
    assert!(ids2.windows(2).all(|w| uf.find(w[0]) == uf.find(w[1])));
    assert_ne!(uf.find(ids1[0]), uf.find(ids2[0]));

    uf.union(ids1[5], ids2[20]);

    let target = uf.find(ids1[0]);
    assert!(ids1
        .iter()
        .chain(ids2.iter())
        .all(|&id| uf.find(id) == target));
}

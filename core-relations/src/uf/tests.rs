use crate::{
    common::{NumericId, Value},
    pool::PoolSet,
    table_spec::{ColumnId, Constraint, Table},
    uf::UnionFind,
};

use super::DisplacedTable;

fn v(x: usize) -> Value {
    Value::from_usize(x)
}

#[test]
fn basic_uf() {
    let mut uf = UnionFind::default();
    let ids1 = (0..100).map(v).collect::<Vec<_>>();
    let ids2 = (100..200).map(v).collect::<Vec<_>>();

    for ids in [&ids1, &ids2] {
        ids.windows(2).for_each(|w| {
            let (parent, child) = uf.union(w[0], w[1]);
            assert_eq!(uf.find(w[0]), parent);
            assert_eq!(uf.find(w[1]), parent);
            assert!(child == w[0] || child == w[1]);
        });
    }

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

#[test]
fn displaced() {
    empty_execution_state!(e);
    let ps = PoolSet::default();
    let mut d = DisplacedTable::default();
    d.stage_insert(&[v(0), v(1), v(0)]);
    d.stage_insert(&[v(2), v(3), v(0)]);
    d.merge(&mut e);
    let all = d.all(&ps);
    let updates = Vec::from_iter(d.scan(&all, &ps).iter().map(|(_, row)| {
        assert_eq!(row[2], v(0));
        (row[0], row[1])
    }));
    assert_eq!(updates.len(), 2);
    assert_ne!(updates[0], updates[1]);
    let eq_fst = d.refine(
        all,
        &[Constraint::EqConst {
            col: ColumnId::new(0),
            val: updates[0].0,
        }],
        &ps,
    );
    let rows = Vec::from_iter(d.scan(&eq_fst, &ps).iter().map(|(_, row)| {
        assert_eq!(row.len(), 3);
        (row[0], row[1], row[2])
    }));
    assert_eq!(rows, vec![(updates[0].0, updates[0].1, v(0))]);

    d.stage_insert(&[v(1), v(3), v(1)]);
    d.merge(&mut e);

    let all = d.all(&ps);
    let updates_2 = Vec::from_iter(d.scan(&all, &ps).iter().map(|(_, row)| (row[0], row[1])));
    assert!(updates_2.windows(2).all(|x| x[0].1 == x[1].1));
}

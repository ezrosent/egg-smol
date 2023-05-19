use std::cmp;

use bumpalo::Bump;

use crate::{
    common::NumericId,
    free_join::AtomIdx,
    function::{
        index::{ConstantIndex, ConstantIndexArg, Index},
        offsets::RangeOrSlice,
        table::{Generation, Table},
    },
    pool::{Clear, PoolSet},
    schema::{ColumnTy, PrimitiveId, Schema},
    uf::UpdateTrackingUnionFind,
};

use super::{
    offsets::{Offset, OffsetRange, Offsets, SortedOffsetVector},
    table::Timestamp,
    Value,
};

fn v(u: usize) -> Value {
    Value::from_usize(u)
}

fn t(u: usize) -> Timestamp {
    Timestamp::from_usize(u)
}

fn o(u: usize) -> Offset {
    Offset::from_usize(u)
}

fn merge_min(n: Value) -> impl Fn(Option<Value>) -> Value {
    move |prev| match prev {
        Some(prev) => {
            if prev < n {
                prev
            } else {
                n
            }
        }
        None => n,
    }
}

fn schema(arity: usize) -> Schema {
    Schema::new((0..arity).map(|_| ColumnTy::Id), ColumnTy::Id)
}

fn range_size(table: &Table, low: Timestamp, hi: Timestamp) -> usize {
    table.timestamp_range(low, hi).size()
}

#[test]
fn basic_insert_lookup() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema(1), t(0), &pool_set);
    table.insert(&[v(0)], merge_min(v(1)));
    assert_eq!(table.get(&[v(0)]), Some(v(1)));
    assert_eq!(table.get(&[v(1)]), None);
    assert_eq!(table.len(), 1);

    table.update_timestamp(t(2));
    table.insert(&[v(0)], merge_min(v(0)));
    assert_eq!(table.get(&[v(0)]), Some(v(0)));
    assert_eq!(table.len(), 1);
}

#[test]
fn insert_many() {
    let mut uf = UpdateTrackingUnionFind::default();
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema(2), t(0), &pool_set);
    for i in 0..100 {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    for i in 0..100 {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    for i in 0..100 {
        assert_eq!(table.get(&[v(i), v(i + 1)]), Some(v(i + 2)));
        assert!(table.get(&[v(i), v(i)]).is_none());
    }

    table.rebuild(t(0), &mut uf, |_, _, _| panic!("should never be called"));

    table.update_timestamp(t(1));
    assert_eq!(range_size(&table, t(0), t(1)), 100);
    assert_eq!(range_size(&table, t(1), t(2)), 0);
    for i in 0..100 {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    assert_eq!(range_size(&table, t(0), t(1)), 100);
    assert_eq!(range_size(&table, t(1), t(2)), 0);

    for i in 0..50 {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 1)));
    }

    assert!(range_size(&table, t(0), t(1)) >= 50);
    assert_eq!(range_size(&table, t(1), t(2)), 50);
}

#[test]
fn insert_remove() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema(2), t(0), &pool_set);
    for i in 0..100 {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    for i in 0..50 {
        table.remove(&[v(i), v(i + 1)]);
    }
    for i in 0..100 {
        if i < 50 {
            assert_eq!(table.get(&[v(i), v(i + 1)]), None);
        } else {
            assert_eq!(table.get(&[v(i), v(i + 1)]), Some(v(i + 2)));
        }
    }
}

#[test]
fn basic_rebuild() {
    const N: usize = 100;
    let schema = Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Primitive(PrimitiveId::new(0)),
    );
    let mut uf = UpdateTrackingUnionFind::default();
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema, t(0), &pool_set);
    let v = (0..N).map(|_| uf.fresh()).collect::<Vec<_>>();

    for v in v.iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }
    for i in 0..N {
        uf.union(v[i], v[i % (N / 2)]);
    }
    uf.advance();
    assert_eq!(uf.recent_reparents.len(), N / 2);
    let mut counter = 0;
    table.rebuild(t(0), &mut uf, |_, l, r| {
        counter += 1;
        cmp::min(l, r)
    });
    OffsetRange::new(Offset::new(0), table.offset_limit()).iter_table(&table, |_, ks, v| {
        for k in ks.iter().copied() {
            assert_eq!(uf.find(k), k);
        }
        assert!(v.index() < (N / 2));
    });
    assert_eq!(counter, N / 2);
}

#[test]
fn rebuild_with_promotions() {
    const N: usize = 100;
    let mut uf = UpdateTrackingUnionFind::default();
    let schema = Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Primitive(PrimitiveId::new(0)),
    );
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema, t(0), &pool_set);
    let v = (0..N).map(|_| uf.fresh()).collect::<Vec<_>>();
    for v in v[(N / 2)..N].iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }

    table.update_timestamp(t(1));
    for v in v[0..(N / 2)].iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }

    for i in 0..N {
        if i % 2 == 0 {
            uf.union(v[i], v[i % (N / 2)]);
        } else {
            uf.union(v[i % (N / 2)], v[i]);
        }
    }
    uf.advance();
    assert_eq!(uf.recent_reparents.len(), N / 2);
    let mut counter = 0;
    table.rebuild(t(1), &mut uf, |_, l, r| {
        counter += 1;
        cmp::min(l, r)
    });
    OffsetRange::new(Offset::new(0), table.offset_limit()).iter_table(&table, |_, ks, v| {
        for k in ks.iter().copied() {
            assert_eq!(uf.find(k), k);
        }
        assert!(v.index() < (N / 2), "{v:?}");
    });
    assert_eq!(counter, N / 2);
}

#[test]
fn rebuild_multi_merge() {
    const N: usize = 10;
    let mut uf = UpdateTrackingUnionFind::default();
    let schema = Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Primitive(PrimitiveId::new(0)),
    );
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema, t(0), &pool_set);
    let v = (0..N).map(|_| uf.fresh()).collect::<Vec<_>>();
    for v in v[(N / 2)..N].iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }

    table.update_timestamp(t(1));
    for v in v[0..(N / 2)].iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }
    {
        v[0..(N / 2)].windows(2).for_each(|w| {
            uf.union(w[0], w[1]);
        });
        uf.advance();
        table.rebuild(t(1), &mut uf, |_, l, r| cmp::min(l, r));
        v.windows(2).for_each(|w| {
            uf.union(w[0], w[1]);
        });
        uf.advance();
        table.rebuild(t(1), &mut uf, |_, l, r| cmp::min(l, r));
    }

    let canon = uf.find(v[0]);
    let mut counter = 0;
    OffsetRange::new(Offset::new(0), table.offset_limit()).iter_table(&table, |_, ks, v| {
        counter += 1;
        for k in ks {
            assert_eq!(*k, canon);
        }
        assert_eq!(v, Value::new(0));
    });
    assert_eq!(counter, 1);
    assert_eq!(table.len(), 1);
}

#[test]
fn rebuild_multi_merge_in_place() {
    const N: usize = 10;
    let mut uf = UpdateTrackingUnionFind::default();
    let schema = Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Primitive(PrimitiveId::new(0)),
    );
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema, t(0), &pool_set);
    let v = (0..N).map(|_| uf.fresh()).collect::<Vec<_>>();
    for v in v[0..N].iter().copied() {
        table.insert(&[v, v], merge_min(v));
    }
    v.windows(2).for_each(|w| {
        uf.union(w[0], w[1]);
    });
    uf.advance();
    let canon = uf.find(v[0]);
    let mut counter = 0;
    table.rebuild(t(0), &mut uf, |_, l, r| cmp::min(l, r));
    OffsetRange::new(Offset::new(0), table.offset_limit()).iter_table(&table, |_, ks, v| {
        counter += 1;
        for k in ks {
            assert_eq!(*k, canon);
        }
        assert_eq!(v, Value::new(0));
    });
    assert_eq!(counter, 1);
    assert_eq!(table.len(), 1);
}

#[test]
fn skipped_timestamp() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    const N: usize = 100;
    let mut table = Table::new(&schema(2), t(0), &pool_set);
    for i in 0..N {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }

    table.update_timestamp(t(1));
    for i in N..(N * 3) {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 3)));
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    assert_eq!(range_size(&table, t(0), t(1)), N);
    assert_eq!(range_size(&table, t(1), t(2)), N * 3);

    table.update_timestamp(t(2));

    for i in N..(N * 5) {
        table.insert(&[v(i), v(i + 1)], merge_min(v(i + 1)));
    }

    assert!(range_size(&table, t(0), t(1)) >= N);
    assert_eq!(range_size(&table, t(2), t(3)), N * 4);
    assert!(range_size(&table, t(1), t(2)) < (N * 4));
}

#[test]
fn iteration() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut table = Table::new(&schema(1), t(0), &pool_set);
    table.insert(&[v(1)], merge_min(v(2)));
    let mut called = false;
    for (key, val) in table.iter() {
        assert!(!called);
        assert_eq!(key, &[v(1)]);
        assert_eq!(val, v(2));
        called = true;
    }
    assert!(called);

    table.insert(&[v(2)], merge_min(v(3)));
    table.insert(&[v(3)], merge_min(v(4)));
    table.insert(&[v(5)], merge_min(v(6)));

    table.update_timestamp(t(2));
    table.insert(&[v(1)], merge_min(v(1)));

    assert_eq!(
        dump_values(table.iter()),
        vec![(vec![1], 1), (vec![2], 3), (vec![3], 4), (vec![5], 6)]
    );
}

fn dump_values<'a>(iter: impl Iterator<Item = (&'a [Value], Value)>) -> Vec<(Vec<usize>, usize)> {
    let mut res = iter
        .map(|(ks, v)| {
            (
                Vec::from_iter(ks.iter().copied().map(Value::index)),
                v.index(),
            )
        })
        .collect::<Vec<_>>();
    res.sort();
    res
}

fn collect<T: Clone>(range: &impl Offsets, elts: &[T]) -> Vec<T> {
    let mut res = Vec::new();
    range.iter_slice(elts, |elt| res.push(elt.clone()));
    if !res.is_empty() {
        range.bounds().expect("nonempty range should have bounds");
    }
    res
}

#[test]
fn offset_range() {
    let elts = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let range = OffsetRange::new(o(3), o(7));
    assert_eq!(collect(&range, &elts), vec![3, 4, 5, 6]);
    assert_eq!(
        collect(&RangeOrSlice::<OffsetRange>::Range(range), &elts),
        vec![3, 4, 5, 6]
    );
    assert_eq!(collect(&OffsetRange::new(o(3), o(3)), &elts), vec![]);
}

#[test]
fn offset_vec() {
    let elts = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut v1 = SortedOffsetVector::default();
    v1.push(o(2));
    v1.push(o(4));
    v1.push(o(8));
    v1.push(o(9));
    assert_eq!(collect(&v1, &elts), vec![2, 4, 8, 9]);

    let v2 = SortedOffsetVector::new(vec![o(3), o(2), o(1), o(4)]);
    assert_eq!(collect(&v2, &elts), vec![1, 2, 3, 4]);
    assert_eq!(collect(&RangeOrSlice::Slice(v2), &elts), vec![1, 2, 3, 4]);
}

#[test]
fn offset_filter() {
    let elts = vec![1, 5, 2, 5, 3, 5, 4, 5];
    let v = SortedOffsetVector::new(vec![o(1), o(2), o(3), o(4)]);
    let mut res = SortedOffsetVector::default();
    v.filter(&elts, |x| *x == 5, &mut res);
    assert_eq!(collect(&res, &elts), vec![5, 5]);
    res.clear();
    res.push(o(0));
    v.filter(&elts, |x| *x == 5, &mut res);
    assert_eq!(collect(&res, &elts), vec![1, 5, 5]);
}

#[test]
#[should_panic]
fn bad_offset_range() {
    OffsetRange::new(o(3), o(2));
}

#[test]
#[should_panic]
fn bad_filter_push() {
    let elts = vec![1, 5, 2, 5, 3, 5, 4, 5];
    let v = SortedOffsetVector::new(vec![o(1), o(2), o(3), o(4)]);
    let mut res = SortedOffsetVector::default();
    res.push(o(2));
    v.filter(&elts, |x| *x == 5, &mut res);
}

#[test]
#[should_panic]
fn bad_offset_stride() {
    OffsetRange::new(o(3), o(2));
}

#[test]
#[should_panic]
fn not_sorted_vec_push() {
    let mut v = SortedOffsetVector::default();
    v.push(o(3));
    v.push(o(1));
    v.push(o(2));
}

#[test]
fn index_basic() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    const N: usize = 100;
    let mut table = Table::new(&schema(2), t(0), &pool_set);
    let mut odds = SortedOffsetVector::default();
    let mut evens = SortedOffsetVector::default();
    for i in 0..N {
        let off = Offset::from_usize(i);
        table.insert(&[v(i % 2), v(i)], merge_min(v(i + 2)));
        if i % 2 == 0 {
            evens.push(off);
        } else {
            odds.push(off);
        }
    }
    let mut index = Index::new(
        pool_set.get(),
        vec![AtomIdx::new(0)],
        vec![],
        &table,
        &OffsetRange::new(Offset::new(0), Offset::from_usize(N)),
    );

    assert!(index.get(&[]).is_none());
    assert!(index.get(&[v(3)]).is_none());
    assert_eq!(&**index.get(&[v(0)]).unwrap(), &evens);
    assert_eq!(&**index.get(&[v(1)]).unwrap(), &odds);

    for i in 0..(N / 5) {
        table.insert(&[v(i % 2), v(i)], merge_min(v(i + 1)));
    }
    assert_eq!(table.generation(), Generation::new(0));

    index.extend(
        &table,
        &OffsetRange::new(Offset::from_usize(N), table.offset_limit()),
    );
    let mut count = 0;
    let v0 = v(0);
    index.get(&[v0]).unwrap().iter_table(&table, |_, k, _| {
        assert_eq!(k[0], v0);
        count += 1;
    });
    assert_eq!(count, N / 2);
}

#[test]
fn index_eq() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    const N: usize = 100;
    let mut table = Table::new(&schema(3), t(0), &pool_set);
    for i in 0..N {
        table.insert(&[v(i), v(i), v(i + 1)], merge_min(v(i + 2)));
    }
    for i in 0..N {
        table.insert(&[v(i + 1), v(i + 1), v(i)], merge_min(v(i + 1)));
    }
    let index1 = Index::new(
        pool_set.get(),
        vec![AtomIdx::new(0)],
        vec![(AtomIdx::new(0), AtomIdx::new(1))],
        &table,
        &OffsetRange::new(Offset::new(0), table.offset_limit()),
    );

    let mut count = 0;
    for (_, v) in index1.iter() {
        v.iter_table(&table, |_, k, _| {
            count += 1;
            assert_eq!(k[0], k[1]);
        });
    }
    assert_eq!(count, N * 2);
    count = 0;

    let index2 = Index::new(
        pool_set.get(),
        vec![AtomIdx::new(1)],
        vec![
            (AtomIdx::new(0), AtomIdx::new(1)),
            (AtomIdx::new(1), AtomIdx::new(3)),
        ],
        &table,
        &OffsetRange::new(Offset::new(0), table.offset_limit()),
    );
    for (_, v) in index2.iter() {
        v.iter_table(&table, |_, k, v| {
            count += 1;
            assert_eq!(k[0], k[1]);
            assert_eq!(k[1], v);
        });
    }
    assert_eq!(count, N);
}

#[test]
fn constant_index_basic() {
    let bump = Bump::new();
    let poolset = PoolSet::new(&bump);
    const N: usize = 100;
    let mut table = Table::new(&schema(2), t(0), &poolset);
    let mut one_threes = SortedOffsetVector::default();
    let mut evens = SortedOffsetVector::default();
    for i in 0..N {
        let off = Offset::from_usize(i);
        table.insert(&[v(i % 2), v(i)], merge_min(v(i % 3)));
        if i % 2 == 0 {
            evens.push(off);
        } else if i % 3 == 0 && i % 2 == 1 {
            one_threes.push(off);
        }
    }
    let mut i0 = poolset.get::<ConstantIndex>().get(&ConstantIndexArg {
        cols: &[(AtomIdx::new(0), v(0))],
        eqs: &[],
    });

    let mut i13 = poolset.get::<ConstantIndex>().get(&ConstantIndexArg {
        cols: &[(AtomIdx::new(0), v(1)), (AtomIdx::new(2), v(0))],
        eqs: &[],
    });

    assert!(i0.offsets().bounds().is_none());
    assert!(i13.offsets().bounds().is_none());

    i0.extend(
        &table,
        &OffsetRange::new(Offset::new(0), table.offset_limit()),
    );

    assert_eq!(i0.offsets(), evens.slice());

    i13.extend(
        &table,
        &OffsetRange::new(Offset::new(0), table.offset_limit()),
    );

    assert_eq!(i13.offsets(), one_threes.slice());

    let old_limit = table.offset_limit();

    for i in N..N * 2 {
        let off = Offset::from_usize(i);
        table.insert(&[v(i % 2), v(i)], merge_min(v(i % 3)));
        if i % 2 == 0 {
            evens.push(off);
        } else if i % 3 == 0 && i % 2 == 1 {
            one_threes.push(off);
        }
    }

    i0.extend(&table, &OffsetRange::new(old_limit, table.offset_limit()));

    assert_eq!(i0.offsets(), evens.slice());

    i13.extend(&table, &OffsetRange::new(old_limit, table.offset_limit()));

    assert_eq!(i13.offsets(), one_threes.slice());
}

#[test]
fn constant_index_eq() {
    let bump = Bump::new();
    let poolset = PoolSet::new(&bump);
    const N: usize = 100;
    let mut table = Table::new(&schema(3), t(0), &poolset);
    let mut targets = SortedOffsetVector::default();
    for i in 0..N {
        let off = table.offset_limit();
        table.insert(&[v(i % 2), v(i), v(i)], merge_min(v(i % 3)));
        table.insert(&[v(i % 2), v(i), v(i + 1)], merge_min(v(i % 3)));
        if i % 2 == 0 {
            targets.push(off);
        }
    }
    let mut i0 = poolset.get::<ConstantIndex>().get(&ConstantIndexArg {
        cols: &[(AtomIdx::new(0), v(0))],
        eqs: &[(AtomIdx::new(2), AtomIdx::new(1))],
    });

    assert!(i0.offsets().bounds().is_none());

    i0.extend(
        &table,
        &OffsetRange::new(Offset::new(0), table.offset_limit()),
    );

    assert_eq!(i0.offsets(), targets.slice());

    let old_limit = table.offset_limit();

    for i in N..N * 2 {
        let off = table.offset_limit();
        table.insert(&[v(i % 2), v(i), v(i)], merge_min(v(i % 3)));
        table.insert(&[v(i % 2), v(i), v(i + 1)], merge_min(v(i % 3)));
        if i % 2 == 0 {
            targets.push(off);
        }
    }

    i0.extend(&table, &OffsetRange::new(old_limit, table.offset_limit()));

    assert_eq!(i0.offsets(), targets.slice());
}

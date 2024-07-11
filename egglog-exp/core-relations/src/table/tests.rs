use crate::{
    common::Value,
    offsets::{RowId, SubsetRef},
    pool::PoolSet,
    row_buffer::TaggedRowBuffer,
    table_shortcuts::{fill_table, v},
    table_spec::{ColumnId, Constraint, Offset, Table, WrappedTable},
};

fn dump_buf(buf: &TaggedRowBuffer) -> Vec<(RowId, Vec<Value>)> {
    let mut res = Vec::new();
    buf.iter()
        .for_each(|(id, row)| res.push((id, row.to_vec())));
    res
}

fn dump_subset(table: &impl Table, subset: SubsetRef) -> Vec<(RowId, Vec<Value>)> {
    let mut res = Vec::new();
    table.scan_generic(subset, |id, row| {
        res.push((id, row.to_vec()));
    });
    res
}

#[test]
fn insert_scan() {
    let pool_set = PoolSet::default();
    let table = fill_table(
        vec![
            vec![v(0), v(1), v(2)],
            vec![v(1), v(2), v(3)],
            vec![v(2), v(3), v(4)],
            vec![v(3), v(4), v(5)],
            vec![v(2), v(3), v(6)],
        ],
        2,
        None,
        |_, new| Some(new.to_vec()),
    );

    let all = table.all(&pool_set);
    let smaller = table.refine_one(
        all,
        &Constraint::GtConst {
            col: ColumnId::new(2),
            val: v(4),
        },
        &pool_set,
    );
    let rows = dump_subset(&table, smaller.as_ref());
    assert_eq!(
        rows,
        vec![
            (RowId::new(3), vec![v(3), v(4), v(5)]),
            (RowId::new(4), vec![v(2), v(3), v(6)])
        ]
    );
    let mut buf = TaggedRowBuffer::new(2, &pool_set);
    let table = WrappedTable::new(table);
    table.scan_project(
        smaller.as_ref(),
        &[ColumnId::new(1), ColumnId::new(0)],
        Offset::new(0),
        usize::MAX,
        &[],
        &mut buf,
    );

    let projection = dump_buf(&buf);
    assert_eq!(
        projection,
        vec![
            (RowId::new(3), vec![v(4), v(3)]),
            (RowId::new(4), vec![v(3), v(2)])
        ]
    );
}

#[test]
fn insert_scan_sorted() {
    let pool_set = PoolSet::default();
    let table = fill_table(
        vec![
            vec![v(0), v(1), v(2)],
            vec![v(1), v(2), v(3)],
            vec![v(2), v(3), v(4)],
            vec![v(3), v(4), v(5)],
            vec![v(2), v(3), v(6)],
        ],
        2,
        Some(ColumnId::new(2)),
        |_, new| Some(new.to_vec()),
    );

    let all = table.all(&pool_set);
    let smaller = table.refine_one(
        all,
        &Constraint::LtConst {
            col: ColumnId::new(1),
            val: v(4),
        },
        &pool_set,
    );
    let rows = dump_subset(&table, smaller.as_ref());
    assert_eq!(
        rows,
        vec![
            (RowId::new(0), vec![v(0), v(1), v(2)]),
            (RowId::new(1), vec![v(1), v(2), v(3)]),
            (RowId::new(4), vec![v(2), v(3), v(6)]),
        ]
    );

    let all = table.all(&pool_set);
    let sorted_smaller = table.refine_one(
        all,
        &Constraint::LtConst {
            col: ColumnId::new(2),
            val: v(5),
        },
        &pool_set,
    );
    let rows = dump_subset(&table, sorted_smaller.as_ref());
    assert_eq!(
        rows,
        vec![
            (RowId::new(0), vec![v(0), v(1), v(2)]),
            (RowId::new(1), vec![v(1), v(2), v(3)]),
        ]
    );
}

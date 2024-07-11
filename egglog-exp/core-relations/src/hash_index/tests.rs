use crate::{
    pool::PoolSet,
    table_shortcuts::{fill_table, v},
    table_spec::{ColumnId, WrappedTable},
    TupleIndex,
};

use super::Index;

#[test]
fn basic_updates() {
    // fill a SortedWritesTable with some data. confirm that an index built on
    // some subset of columns works as expected. Then add more data, and confirm
    // that updates still work.
    let ps = PoolSet::default();
    let mut table = WrappedTable::new(fill_table(
        vec![
            vec![v(0), v(1), v(2), v(0)],
            vec![v(1), v(2), v(3), v(0)],
            vec![v(2), v(3), v(4), v(0)],
            vec![v(3), v(4), v(5), v(1)],
            vec![v(4), v(5), v(6), v(1)],
        ],
        2,
        Some(ColumnId::new(3)),
        |old, new| {
            assert_eq!(old, new, "no conflicts in this test");
            None
        },
    ));

    let mut index = Index::new(
        vec![ColumnId::new(0), ColumnId::new(2)],
        TupleIndex::new(2, &ps),
    );
    assert!(index.get_subset(&[v(0), v(2)]).is_none());
    index.refresh(&table, &ps);
    for i in 0..=4 {
        let key = [v(i), v(i + 2)];
        let subset = index.get_subset(&key).unwrap();
        table.scan(subset, &ps).iter().for_each(|(id, row)| {
            assert_eq!(&row[0..3], &[v(i), v(i + 1), v(i + 2)]);
            let readback = table.get_row(&row[0..2], &ps).expect("row should exist");
            assert_eq!(readback.id, id);
            assert_eq!(readback.vals.as_slice(), row);
        });
    }

    for i in 5..10 {
        table.stage_insert(&[v(i), v(i + 1), v(i + 2), v(2)]);
    }

    empty_execution_state!(es);
    table.merge(&mut es);
    index.refresh(&table, &ps);
    for i in 0..10 {
        let key = [v(i), v(i + 2)];
        let subset = index.get_subset(&key).unwrap();
        table.scan(subset, &ps).iter().for_each(|(id, row)| {
            assert_eq!(&row[0..3], &[v(i), v(i + 1), v(i + 2)]);
            let readback = table.get_row(&row[0..2], &ps).expect("row should exist");
            assert_eq!(readback.id, id);
            assert_eq!(readback.vals.as_slice(), row);
        });
    }

    // Now get an update to the major version.
    let start_version = table.version().major;
    while table.version().major == start_version {
        table.stage_remove(&[v(0), v(1)]);
        table.merge(&mut es);
        table.stage_insert(&[v(0), v(1), v(2), v(3)]);
        table.merge(&mut es);
    }

    // Refresh should do the right thing.
    index.refresh(&table, &ps);
    for i in 0..10 {
        let key = [v(i), v(i + 2)];
        let subset = index.get_subset(&key).unwrap();
        table.scan(subset, &ps).iter().for_each(|(id, row)| {
            assert_eq!(&row[0..3], &[v(i), v(i + 1), v(i + 2)]);
            let readback = table.get_row(&row[0..2], &ps).expect("row should exist");
            assert_eq!(readback.id, id);
            assert_eq!(readback.vals.as_slice(), row);
        });
    }
}

//! Utilities helpful in unit tests for manipulating tables.

use numeric_id::NumericId;

use crate::{
    common::Value,
    pool::PoolSet,
    table::SortedWritesTable,
    table_spec::{ColumnId, Table},
};

/// A very basic macro just used to initialize an ExecutionState for tests that
/// do not actually use one.
macro_rules! empty_execution_state {
    ($es:ident) => {
        let mut __db = $crate::free_join::Database::default();
        let mut __pv = $crate::action::PredictedVals::default();
        let mut $es = $crate::action::ExecutionState {
            db: &mut __db,
            predicted: &mut __pv,
        };
    };
}

/// Shorthand for generating a [`Value`].
pub(crate) fn v(n: usize) -> Value {
    Value::from_usize(n)
}

/// Fill a [`SortedWritesTable`] with the given rows, with conflicts resolved
/// with the given merg function.
pub(crate) fn fill_table(
    rows: impl IntoIterator<Item = Vec<Value>>,
    n_keys: usize,
    sort_by: Option<ColumnId>,
    merge_fn: impl Fn(&[Value], &[Value]) -> Option<Vec<Value>> + 'static,
) -> SortedWritesTable {
    empty_execution_state!(e);
    let pool_set = PoolSet::default();
    let mut iter = rows.into_iter();
    let init = iter.next().expect("iterator must be nonempty");
    let n_cols = init.len();
    assert!(n_cols >= n_keys, "must have at least {n_keys} columns");
    let mut table = SortedWritesTable::new(
        n_keys,
        n_cols,
        sort_by,
        move |_, old, new, out| {
            if let Some(res) = merge_fn(old, new) {
                *out = res;
                true
            } else {
                false
            }
        },
        &pool_set,
    );
    table.stage_insert(&init);
    for row in iter {
        table.stage_insert(&row);
    }
    table.merge(&mut e);
    table
}

//! Data-structures for representing functions / relations.

use crate::{
    define_id,
    pool::PoolSet,
    schema::{ColumnTy, Schema},
    uf::UpdateTrackingUnionFind,
};

use self::table::{Table, Timestamp};

pub(crate) mod index;
pub(crate) mod index_cache;
pub(crate) mod offsets;
pub(crate) mod table;
#[cfg(test)]
mod tests;

define_id!(pub Value, u32, "A generic identifier representing an egglog value");

const STALE_MASK: u32 = 1 << 31;

impl Value {
    fn set_stale(&mut self) {
        self.rep |= STALE_MASK;
    }

    pub(crate) fn is_stale(&self) -> bool {
        self.rep & STALE_MASK != 0
    }
}

pub(crate) struct Function<'pool> {
    schema: Schema,
    table: table::Table<'pool>,
}

impl<'pool> Function<'pool> {
    pub(crate) fn new(schema: Schema, pool_set: &PoolSet<'pool>) -> Function<'pool> {
        let table = Table::new(&schema, Timestamp::new(0), pool_set);
        Function { schema, table }
    }
    pub(crate) fn insert(
        &mut self,
        vals: &[Value],
        ret: Value,
        ts: Timestamp,
        uf: &mut UpdateTrackingUnionFind<Value>,
    ) {
        self.table.update_timestamp(ts);
        match *self.schema().ret() {
            ColumnTy::Id => {
                self.table.insert(vals, |prev| {
                    if let Some(prev) = prev {
                        uf.union(ret, prev).0
                    } else {
                        ret
                    }
                });
            }
            ColumnTy::Primitive(_) => self.table.insert(vals, |prev| {
                if let Some(prev) = prev {
                    assert_eq!(prev, ret,
                        "merge functions for primitives unsupported: vals={vals:?} prev={prev:?} ret={ret:?}");
                    ret
                } else {
                    ret
                } 
            }),
        }
    }

    pub(crate) fn get(&self, vals: &[Value]) -> Option<Value> {
        self.table.get(vals)
    }

    pub(crate) fn get_with_default(
        &mut self,
        vals: &[Value],
        ts: Timestamp,
        uf: &mut UpdateTrackingUnionFind<Value>,
        default: impl FnOnce(&mut UpdateTrackingUnionFind<Value>) -> Value,
    ) -> Value {
        if let Some(prev) = self.table.get(vals) {
            prev
        } else {
            let ret = default(uf);
            self.insert(vals, ret, ts, uf);
            ret
        }
    }

    pub(crate) fn table(&self) -> &table::Table<'pool> {
        &self.table
    }
    pub(crate) fn table_mut(&mut self) -> &mut table::Table<'pool> {
        &mut self.table
    }
    pub(crate) fn schema(&self) -> &Schema {
        &self.schema
    }
}

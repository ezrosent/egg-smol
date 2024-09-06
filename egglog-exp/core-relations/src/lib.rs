#[macro_use]
#[cfg(test)]
pub(crate) mod table_shortcuts;
pub(crate) mod action;
pub(crate) mod common;
pub(crate) mod free_join;
pub(crate) mod hash_index;
pub(crate) mod offsets;
pub(crate) mod pool;
pub(crate) mod primitives;
pub(crate) mod query;
pub(crate) mod row_buffer;
pub(crate) mod table;

pub(crate) mod table_spec;
pub(crate) mod uf;

#[cfg(test)]
mod tests;

pub use action::{ExecutionState, MergeVal, QueryEntry, WriteVal};
pub use common::Value;
pub use free_join::{
    plan::PlanStrategy, CounterId, Database, ExternalFunction, ExternalFunctionId, TableId,
    Variable,
};
pub use hash_index::TupleIndex;
pub use offsets::{OffsetRange, RowId, Subset, SubsetRef};
pub use pool::{Pool, PoolSet, Pooled};
pub use primitives::{
    PrimitiveFunctionId, PrimitiveFunctionSignature, PrimitiveId, PrimitivePrinter, Primitives,
};
pub use query::{QueryBuilder, QueryError, RuleBuilder, RuleSet, RuleSetBuilder};
pub use row_buffer::TaggedRowBuffer;
pub use table::SortedWritesTable;
pub use table_spec::{
    ColumnId, Constraint, Offset, Row, Table, TableSpec, TableVersion, WrappedTable,
};
pub use uf::{DisplacedTable, DisplacedTableWithProvenance, ProofReason, ProofStep};

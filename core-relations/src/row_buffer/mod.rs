//! A basic data-structure encapsulating a batch of rows.

use smallvec::SmallVec;

use crate::{
    common::{NumericId, Value},
    offsets::RowId,
    pool::{PoolSet, Pooled},
};

#[cfg(test)]
mod tests;

/// A batch of rows. This is a common enough pattern that it makes sense to make
/// it its own data-structure. The advantage of this abstraction is that it
/// allows us to store multiple rows in a single allocation.
///
/// RowBuffer stores data in row-major order.
pub(crate) struct RowBuffer {
    n_columns: usize,
    total_rows: usize,
    data: Pooled<Vec<Value>>,
}

impl RowBuffer {
    /// Create a new RowBuffer with the given arity.
    pub(crate) fn new(n_columns: usize, pool_set: &PoolSet) -> RowBuffer {
        assert_ne!(
            n_columns, 0,
            "attempting to create a row batch with no columns"
        );
        RowBuffer {
            n_columns,
            total_rows: 0,
            data: pool_set.get(),
        }
    }

    /// Return an iterator over the non-stale rows in the buffer.
    pub(crate) fn non_stale(&self) -> impl Iterator<Item = &[Value]> {
        self.data
            .chunks(self.n_columns)
            .filter(|row| !row[0].is_stale())
    }

    /// Return an iterator over all rows in the buffer.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &[Value]> {
        self.data.chunks(self.n_columns)
    }

    /// Clear the contents of the buffer.
    pub(crate) fn clear(&mut self) {
        self.data.clear();
        self.total_rows = 0;
    }

    /// The number of rows in the buffer.
    pub(crate) fn len(&self) -> usize {
        self.total_rows
    }

    /// Get the row corresponding to the given RowId.
    ///
    /// # Panics
    /// This method panics if `row` is out of bounds.
    pub(crate) fn get_row(&self, row: RowId) -> &[Value] {
        &self.data[row.index() * self.n_columns..(row.index() + 1) * self.n_columns]
    }

    /// Get a mutable reference to the row corresponding to the given RowId.
    ///
    /// # Panics
    /// This method panics if `row` is out of bounds.
    pub(crate) fn get_row_mut(&mut self, row: RowId) -> &mut [Value] {
        &mut self.data[row.index() * self.n_columns..(row.index() + 1) * self.n_columns]
    }

    /// Set the given row to be stale. By convention, this calls `set_stale` on
    /// the first column in the row. Returns whether the row was already stale.
    ///
    /// # Panics
    /// This method panics if `row` is out of bounds.
    pub(crate) fn set_stale(&mut self, row: RowId) -> bool {
        let row = self.get_row_mut(row);
        let res = row[0].is_stale();
        row[0].set_stale();
        res
    }

    /// Insert a row into a buffer, returning the RowId for this row.
    ///
    /// # Panics
    /// This method panics if the length of `row` does not match the arity of
    /// the RowBuffer.
    pub(crate) fn add_row(&mut self, row: &[Value]) -> RowId {
        assert_eq!(
            row.len(),
            self.n_columns,
            "attempting to add a row with mismatched arity to table"
        );
        if self.total_rows == 0 {
            Pooled::refresh(&mut self.data);
        }
        let res = RowId::from_usize(self.total_rows);
        self.data.extend_from_slice(row);
        self.total_rows += 1;
        res
    }

    /// Remove any stale entries in the buffer. This invalidates existing
    /// RowIds. This method calls `remap` with the old and new RowIds for all
    /// non-stale rows.
    pub(crate) fn remove_stale(&mut self, mut remap: impl FnMut(&[Value], RowId, RowId)) {
        let mut within_row = 0;
        let mut row_in = 0;
        let mut row_out = 0;
        let mut keep_row = true;
        let mut scratch = SmallVec::<[Value; 8]>::new();
        self.data.retain(|entry| {
            if within_row == 0 {
                keep_row = !entry.is_stale();
                if keep_row {
                    scratch.push(*entry);
                    row_out += 1;
                }
                row_in += 1;
            } else if keep_row {
                scratch.push(*entry);
            }
            within_row += 1;
            if within_row == self.n_columns {
                within_row = 0;
                if keep_row {
                    remap(&scratch, RowId::new(row_in - 1), RowId::new(row_out - 1));
                    scratch.clear();
                }
            }
            keep_row
        });
        self.total_rows = row_out as usize;
    }
}

/// A `TaggedRowBuffer` wraps a `RowBuffer` but also keeps track of a _source_
/// `RowId` for the row it contains. This makes it useful for materializing
/// the contents of a `Subset` of a table.
pub struct TaggedRowBuffer {
    inner: RowBuffer,
}

impl TaggedRowBuffer {
    /// Create a new buffer with the given arity.
    pub fn new(n_columns: usize, pool_set: &PoolSet) -> TaggedRowBuffer {
        TaggedRowBuffer {
            inner: RowBuffer::new(n_columns + 1, pool_set),
        }
    }

    /// Clear the contents of the buffer.
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    fn base_arity(&self) -> usize {
        self.inner.n_columns - 1
    }

    /// Add the given row and RowId to the buffer, returning the RowId (in
    /// `self`) for the new row.
    pub fn add_row(&mut self, row_id: RowId, row: &[Value]) -> RowId {
        // Variant of `RowBuffer::add_row` that also stores the given `RowId` inline.
        //
        // Changes to the implementation of one method should probably also
        // change the other.
        assert_eq!(
            row.len(),
            self.base_arity(),
            "attempting to add a row with mismatched arity to table"
        );
        if self.inner.total_rows == 0 {
            Pooled::refresh(&mut self.inner.data);
        }
        let res = RowId::from_usize(self.inner.total_rows);
        self.inner.data.extend_from_slice(row);
        self.inner.data.push(Value::new(row_id.rep()));
        self.inner.total_rows += 1;
        res
    }

    /// Get the row (and the id it was associated with at insertion time) at the
    /// offset associated with `row`.
    pub fn get_row(&self, row: RowId) -> (RowId, &[Value]) {
        self.unwrap_row(self.inner.get_row(row))
    }

    /// Iterate over the contents of the buffer.
    pub fn iter(&self) -> impl Iterator<Item = (RowId, &[Value])> {
        self.inner.iter().map(|row| self.unwrap_row(row))
    }

    /// Iterate over all rows in the buffer, except for the stale ones.
    pub fn iter_non_stale(&self) -> impl Iterator<Item = (RowId, &[Value])> {
        self.inner
            .iter()
            .filter(|x| !x[1].is_stale())
            .map(|row| self.unwrap_row(row))
    }

    fn unwrap_row<'a>(&self, row: &'a [Value]) -> (RowId, &'a [Value]) {
        let row_id = row[self.base_arity()];
        let row = &row[..self.base_arity()];
        (RowId::new(row_id.rep()), row)
    }
}

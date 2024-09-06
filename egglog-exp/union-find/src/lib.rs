//! This crate contains a basic union-find implementation.
//!
//! This is in a separate crate because we use it in a number of places. We may
//! eventually make this better (e.g. with ranks, etc.) but for now this works
//! well enough.
use numeric_id::NumericId;
use std::cmp;

#[cfg(test)]
mod tests;

/// A basic implementation of a union-find datastructure.
#[derive(Clone)]
pub struct UnionFind<Value> {
    parents: Vec<Value>,
}

impl<V> Default for UnionFind<V> {
    fn default() -> Self {
        Self {
            parents: Vec::new(),
        }
    }
}

impl<Value: NumericId> UnionFind<Value> {
    /// Reset the union-find data-structure to the point where all Ids are their
    /// own parents.
    pub fn reset(&mut self) {
        for (i, v) in self.parents.iter_mut().enumerate() {
            *v = Value::from_usize(i);
        }
    }

    /// Reserve sufficient space for the given value `v`.
    pub fn reserve(&mut self, v: Value) {
        if v.index() >= self.parents.len() {
            for i in self.parents.len()..=v.index() {
                self.parents.push(Value::from_usize(i));
            }
        }
    }

    /// Merge two equivalence classes.
    pub fn union(&mut self, a: Value, b: Value) -> (Value /* parent */, Value /* child */) {
        self.reserve(a);
        self.reserve(b);
        let a = self.find(a);
        let b = self.find(b);
        if a != b {
            // TODO: probably want to do union-by-rank here. We need a rule that
            // avoids spurious changes to the database when we create a new id
            // only to immediately union it with a preexisting e-class, at which
            // point things get deduped.
            let parent = cmp::min(a, b);
            let child = cmp::max(a, b);
            self.parents[child.index()] = parent;
            (parent, child)
        } else {
            (a, a)
        }
    }

    /// Find the representative of an equivalence class.
    pub fn find(&mut self, id: Value) -> Value {
        self.reserve(id);
        let mut cur = id;
        loop {
            let parent = self.parents[cur.index()];
            if cur == parent {
                break;
            }
            let grand = self.parents[parent.index()];
            self.parents[cur.index()] = grand;
            cur = grand;
        }
        cur
    }
}

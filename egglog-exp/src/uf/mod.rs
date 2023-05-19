//! A basic union-find data-structure using path halving, without sizes or
//! ranks.
use std::mem;

use crate::common::{IndexSet, NumericId};

#[cfg(test)]
mod tests;

pub(crate) struct UpdateTrackingUnionFind<Id> {
    pub(crate) uf: UnionFind<Id>,
    pub(crate) recent_reparents: IndexSet<Id>,
}

impl<Id> Default for UpdateTrackingUnionFind<Id> {
    fn default() -> UpdateTrackingUnionFind<Id> {
        Self {
            uf: Default::default(),
            recent_reparents: Default::default(),
        }
    }
}

impl<Id: NumericId> UpdateTrackingUnionFind<Id> {
    pub(crate) fn has_pending_changes(&self) -> bool {
        !self.uf.staged_reparents.is_empty() || !self.recent_reparents.is_empty()
    }

    pub(crate) fn fresh(&mut self) -> Id {
        self.uf.fresh()
    }
    pub(crate) fn union(&mut self, a: Id, b: Id) -> (Id /* parent */, Id /* child */) {
        self.uf.union(a, b)
    }
    pub(crate) fn find(&mut self, id: Id) -> Id {
        self.uf.find(id)
    }
    pub(crate) fn advance(&mut self) {
        mem::swap(&mut self.recent_reparents, &mut self.uf.staged_reparents);
        self.uf.staged_reparents.clear();
    }
    pub(crate) fn recent_reparents(&self) -> &IndexSet<Id> {
        &self.recent_reparents
    }
}

pub(crate) struct UnionFind<Id> {
    parents: Vec<Id>,
    staged_reparents: IndexSet<Id>,
}

impl<Id> Default for UnionFind<Id> {
    fn default() -> UnionFind<Id> {
        Self {
            parents: Default::default(),
            staged_reparents: Default::default(),
        }
    }
}

impl<Id: NumericId> UnionFind<Id> {
    /// Create a fresh equivalence class.
    pub(crate) fn fresh(&mut self) -> Id {
        let res = Id::from_usize(self.parents.len());
        self.parents.push(res);
        res
    }

    /// Merge two equivalence classes.
    pub(crate) fn union(&mut self, a: Id, b: Id) -> (Id /* parent */, Id /* child */) {
        let a = self.find(a);
        let b = self.find(b);
        if a != b {
            self.staged_reparents.insert(a);
            self.parents[a.index()] = b;
        }
        (b, a)
    }

    /// Find the representative of an equivalence class.
    pub(crate) fn find(&mut self, id: Id) -> Id {
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

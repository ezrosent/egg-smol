use petgraph::prelude::{NodeIndex, UnGraph};

use crate::Id;

#[derive(Debug, Clone, Default)]
pub(crate) struct EqProofState {
    graph: UnGraph<Id, Justification>,
}

impl EqProofState {
    pub(crate) fn make_set(&mut self, id: Id) {
        debug_assert_eq!(usize::from(id), self.graph.node_count());
        self.graph.add_node(id);
    }
    pub(crate) fn add_reason(&mut self, x: Id, y: Id, reason: Justification) {
        self.graph.add_edge(Self::node(x), Self::node(y), reason);
    }

    fn node(id: Id) -> NodeIndex {
        NodeIndex::new(usize::from(id))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct RuleId(u32);

impl Default for RuleId {
    fn default() -> Self {
        RuleId(5)
    }
}

impl RuleId {
    pub(crate) fn background() -> RuleId {
        RuleId(0)
    }
    pub(crate) fn bare_action() -> RuleId {
        RuleId(1)
    }
    pub(crate) fn calc() -> RuleId {
        RuleId(2)
    }
    pub(crate) fn extract() -> RuleId {
        RuleId(3)
    }

    // NB: this is more of a placeholder before we figure out how to properly
    // handle nontrivial tuples that are added as the result of a merge. It's
    // possible that merge functions just cannot add entries of their own
    // (rather they can "just compute"); this tag will allow us to track when
    // and if this does happen, and go from there.
    pub(crate) fn merge_logic() -> RuleId {
        RuleId(4)
    }
    pub(crate) fn next(&mut self) -> RuleId {
        let res = *self;
        self.0 += 1;
        res
    }
}

#[derive(Debug, Clone)]
pub enum Justification {
    // Not sure how to handle these just yet. This is used as a placeholder in the code
    // Seems like we'd need something like:
    // Merge(RowPtr, RowPtr)
    // Where RowPtr := (Function, stable index into a row)
    // Requires that we have two "stable" pointers for both old and new.
    MergeTodo,
    Base(RuleId),
    Cong(Id, Id),
}

/// A local offset into a function's "old" values.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct RowOffset(u32);

impl RowOffset {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn new(n: usize) -> RowOffset {
        assert!(n <= u32::MAX as usize);
        RowOffset(n as u32)
    }
}

#[derive(Debug, Clone)]
pub enum RowJustification {
    Base(RuleId),
    Rebuilt(RowOffset),
    Merged {
        rebuilt: RowOffset,
        merged: RowOffset,
    },
    // Remove this
    Todo_xxx,
}

// What information do we store in a function output?
// Base(RuleId) [the rule that caused us to write this element]
// Rebuilt(RowPtr) [see above for rowptr]

// And a separate vector of tuples:
// * the values, (including outputs)

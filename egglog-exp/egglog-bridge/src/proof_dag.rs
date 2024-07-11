//! A basic tree-like proof data-structure.
//!
//! The current format here is meant to be inspectable by a human, but the goal
//! is to eventually extend it with proper hooks to make it easier to manipulate
//! programatically.

use std::{collections::HashMap, rc::Rc};

use petgraph::{dot::Dot, graph::NodeIndex, Graph};

use crate::proof_spec::DisplayList;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum RenderedValue {
    Id(usize),
    Prim(String),
}

impl std::fmt::Display for RenderedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RenderedValue::Id(id) => write!(f, "@{id}"),
            RenderedValue::Prim(s) => write!(f, "{s}"),
        }
    }
}

/// Proofs that two values are equal.
#[derive(Debug)]
pub enum EqProof {
    /// An explanation of the existence of a row in the union-find.
    Base(Rc<RowProof>),
    /// A proof that `x = y` by way of `y = x`.
    Backwards(Rc<EqProof>),
    /// A proof that `x = z` by way of `x = y`, `y = z` (for any number of
    /// intermediate `y`s).
    Trans(Vec<Rc<EqProof>>),
    /// A proof that `x = y` because `f(k1, k2, ..., kn) = x` and
    /// `f(k1, k2, ..., kn) = y`.
    Cong {
        func: String,
        x: RenderedValue,
        y: RenderedValue,
        key: Vec<RenderedValue>,
        x_proof: Rc<RowProof>,
        y_proof: Rc<RowProof>,
    },
    // TODO: identity proof that is just a Row proof / projection.
}

/// Proofs explaining the contents of a row.
#[derive(Debug)]
pub enum RowProof {
    /// A proof that a row `r'` exists because:
    /// * Another row `r` exists, and
    /// * Each entry in `r` is equal to `r'`.
    RowEq {
        func: String,
        old_row: Rc<RowProof>,
        new_row: Vec<RenderedValue>,
        eq_proofs: Vec<Rc<EqProof>>,
    },
    /// The base case of a proof. Terms that were added as base values to the
    /// database.
    Fiat {
        desc: String,
        func: String,
        row: Vec<RenderedValue>,
    },
    /// A proof of the existence of a row by applying a rule to the databse.
    Exists {
        rule_desc: String,
        atom_desc: String,
        func: String,
        row: Vec<ElementProof>,
        // TODO: need existence stuff here, e.g. Z below
        // Oliver suggests: have the row (G x y) + Proofs of everything on the
        // LHS (Proof of X(x, y), proof of Z(z))
    },
}

impl RowProof {
    /// Render a graph of `RowProof` in the Dot format.
    pub fn to_dot(&self) -> String {
        let mut builder = GraphBuilder::default();
        builder.translate_row(self);
        format!("{:?}", Dot::new(&builder.graph))
    }
}

#[derive(Default)]
struct GraphBuilder {
    nodes: HashMap<usize, NodeIndex>,
    graph: Graph<GraphNode, Edge>,
}

impl GraphBuilder {
    fn translate_row(&mut self, row: &RowProof) -> NodeIndex {
        let ptr_as_usize = row as *const _ as usize;
        if let Some(&node) = self.nodes.get(&ptr_as_usize) {
            return node;
        }

        let node = match row {
            RowProof::RowEq {
                func,
                old_row,
                new_row,
                eq_proofs,
            } => {
                let node = self.graph.add_node(GraphNode::RowProof {
                    desc: format!(
                        "RowEq, new row: ({func} {})",
                        DisplayList(new_row.clone(), " "),
                    ),
                });
                let old_row = self.translate_row(old_row);
                self.graph.add_edge(node, old_row, Edge::OldRow);
                for (i, eq_proof) in eq_proofs.iter().enumerate() {
                    let eq_node = self.translate_eq(eq_proof);
                    self.graph
                        .add_edge(node, eq_node, Edge::EqProof { index: i });
                }
                node
            }
            RowProof::Fiat { desc, func, row } => self.graph.add_node(GraphNode::RowProof {
                desc: format!("fiat: {desc}, ({func} {})", DisplayList(row.clone(), " ")),
            }),
            RowProof::Exists {
                rule_desc,
                atom_desc,
                func,
                row,
            } => {
                let node = self.graph.add_node(GraphNode::RowProof {
                    desc: format!(
                        "Exists, rule: {rule_desc}, atom: {atom_desc}, ({func} {})",
                        DisplayList(row.iter().map(|x| &x.val).collect(), " "),
                    ),
                });
                for (i, ElementProof { proofs, .. }) in row.iter().enumerate() {
                    for proj in proofs {
                        let proj_node = self.translate_row(&proj.proof);
                        self.graph.add_edge(
                            node,
                            proj_node,
                            Edge::Proj {
                                src_field: i,
                                dst_field: proj.field,
                            },
                        );
                    }
                }
                node
            }
        };
        self.nodes.insert(ptr_as_usize, node);
        node
    }

    fn translate_eq(&mut self, eq: &EqProof) -> NodeIndex {
        let ptr_as_usize = eq as *const _ as usize;
        if let Some(&node) = self.nodes.get(&ptr_as_usize) {
            return node;
        }
        let node = match eq {
            EqProof::Base(x) => {
                let node = self.graph.add_node(GraphNode::EqProof {
                    desc: "row-eq".to_string(),
                });
                let child = self.translate_row(x);
                self.graph.add_edge(node, child, Edge::EqChild { index: 0 });
                node
            }
            EqProof::Backwards(eq) => {
                let node = self.graph.add_node(GraphNode::EqProof {
                    desc: "rev".to_string(),
                });
                let child = self.translate_eq(eq);
                self.graph.add_edge(node, child, Edge::EqChild { index: 0 });
                node
            }
            EqProof::Trans(children) => {
                let node = self.graph.add_node(GraphNode::EqProof {
                    desc: if children.is_empty() { "id" } else { "trans" }.to_string(),
                });
                for (index, child) in children.iter().enumerate() {
                    let child_node = self.translate_eq(child);
                    self.graph
                        .add_edge(node, child_node, Edge::EqChild { index });
                }
                node
            }
            EqProof::Cong {
                func,
                x,
                y,
                key,
                x_proof,
                y_proof,
            } => {
                let node = self.graph.add_node(GraphNode::EqProof {
                    desc: format!(
                        "congruence: ({func} {}) = {x} and {y}",
                        DisplayList(key.clone(), " ")
                    ),
                });
                let x_node = self.translate_row(x_proof);
                let y_node = self.translate_row(y_proof);
                self.graph
                    .add_edge(node, x_node, Edge::EqProof { index: 0 });
                self.graph
                    .add_edge(node, y_node, Edge::EqProof { index: 1 });
                node
            }
        };
        self.nodes.insert(ptr_as_usize, node);
        node
    }
}

// (rule ((= _ (X x y))) ((G x y) (F y))) ; rule = R

// X(x, y), Z(z) => G(x, y), F(y)
// T(x, y, z) => id' = Add(x, y), id = Add(id', z)
// T(x, y, z), id' = Add(x, y) => id = Add(id', z)
// Proof-G(x) = {x: Project(0, Proof-X(x, y)), y: Project(1, Proof-X(x, y))}
// Proof-F(x) = {y: Project(1, Proof-X(x, y))}

#[derive(Debug)]
pub struct ElementProof {
    pub val: RenderedValue,
    pub proofs: Vec<Projection>,
}

/// A reference to a particular column in the proof of a given row.
#[derive(Debug)]
pub struct Projection {
    pub field: usize,
    pub proof: Rc<RowProof>,
}

// We allow dead code here as the unused fields are used by `Debug` and printed
// when outputting Dot files.
#[derive(Debug)]
#[allow(dead_code)]
enum GraphNode {
    RowProof { desc: String },

    EqProof { desc: String },
}

#[derive(Debug)]
#[allow(dead_code)]
enum Edge {
    Proj { src_field: usize, dst_field: usize },
    OldRow,
    EqProof { index: usize },
    EqChild { index: usize },
    Trans { index: usize },
}

use std::collections::HashMap;

use egg::{Analysis, Id, Language, RecExpr};
use petgraph::{stable_graph::NodeIndex, visit::EdgeRef};
use zdds::{Dag, ExtractResult};

pub fn extract_zdd<L, A>(
    e: &egg::EGraph<L, A>,
    root: Id,
    get_cost: impl FnMut(&egg::EGraph<L, A>, &L) -> f64,
    node_limit: Option<usize>,
) -> Option<RecExpr<L>>
where
    L: Language,
    A: Analysis<L>,
{
    let mut extractor = ExtractorEgraph::new(e, get_cost);
    let (result, _) = zdds::extract_zdd(&mut extractor, root, node_limit)?;
    Some(extractor.to_recexpr(&result))
}

type NodeId = usize;
type ClassId = Id;

struct ExtractorEgraph<L> {
    classes: HashMap<Id, Vec<NodeId>>,
    nodes: Vec<(L, f64)>,
}

impl<L: Language> ExtractorEgraph<L> {
    fn new<A: Analysis<L>>(
        egraph: &egg::EGraph<L, A>,
        mut get_cost: impl FnMut(&egg::EGraph<L, A>, &L) -> f64,
    ) -> Self {
        let mut classes = HashMap::new();
        let mut nodes = vec![];
        for class in egraph.classes() {
            let mut class_nodes = vec![];
            for node in &class.nodes {
                let node_id = nodes.len();
                let cost = get_cost(egraph, node);
                nodes.push((node.clone(), cost));
                class_nodes.push(node_id);
            }
            classes.insert(class.id, class_nodes);
        }
        Self { classes, nodes }
    }

    fn to_recexpr(&self, result: &ExtractResult<NodeId>) -> RecExpr<L> {
        let mut res = RecExpr::default();
        let mut memo = HashMap::default();
        self.to_recexpr_inner(&result.dag, &mut memo, &mut res, result.root);
        res
    }

    fn to_recexpr_inner(
        &self,
        dag: &Dag<NodeId>,
        memo: &mut HashMap<NodeId, Id>,
        res: &mut RecExpr<L>,
        node: NodeIndex,
    ) -> Id {
        let node_id = *dag.node_weight(node).unwrap();
        if let Some(id) = memo.get(&node_id) {
            return *id;
        }
        let mut lang_node = self.nodes[node_id].0.clone();
        let mut edges = Vec::new();
        for edge in dag.edges(node) {
            edges.push((*edge.weight(), edge.target()));
        }
        edges.sort_by_key(|(x, _)| *x);
        for ((_, child_node), child_cell) in edges.into_iter().zip(lang_node.children_mut()) {
            *child_cell = self.to_recexpr_inner(dag, memo, res, child_node);
        }
        let id = res.add(lang_node);
        memo.insert(node_id, id);
        id
    }
}

impl<L: Language> zdds::Egraph for ExtractorEgraph<L> {
    type EClassId = ClassId;
    type ENodeId = NodeId;

    fn expand_class(&mut self, class: &ClassId, nodes: &mut Vec<NodeId>) {
        nodes.extend_from_slice(&self.classes[class])
    }

    fn get_children(&mut self, node: &NodeId, classes: &mut Vec<ClassId>) {
        classes.extend_from_slice(self.nodes[*node].0.children())
    }

    fn cost_f64(&self, node: &NodeId) -> f64 {
        self.nodes[*node].1
    }
}

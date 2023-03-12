use petgraph::{prelude::NodeIndex, visit::Dfs};

use crate::{
    egraph::{ExtractResult, Pool},
    Dag, Egraph, HashMap, HashSet,
};

pub fn extract_greedy<E: Egraph>(
    egraph: &mut E,
    root: E::EClassId,
) -> Option<ExtractResult<E::ENodeId>> {
    let mut extractor = Extractor {
        graph: Default::default(),
        hashcons: Default::default(),
        egraph,
    };
    let pool = Pool::default();
    let (root_node, _) = extractor.traverse_class(root, &pool)?;
    let total_cost = extractor.prune_and_compute_cost(root_node);
    Some(ExtractResult {
        root: root_node,
        dag: extractor.graph,
        total_cost,
    })
}

struct Extractor<'a, E: Egraph> {
    graph: Dag<E::ENodeId>,
    hashcons: HashMap<E::ENodeId, Option<(NodeIndex, usize)>>,
    egraph: &'a mut E,
}

impl<'a, E: Egraph> Extractor<'a, E> {
    fn prune_and_compute_cost(&mut self, root: NodeIndex) -> usize {
        // We don't want to use the cost in `hashcons` because it can
        // double-count nodes that have multiple parents in the DAG.
        let mut cost = 0usize;
        let mut visited = HashSet::default();
        let mut dfs = Dfs::new(&self.graph, root);
        while let Some(n) = dfs.next(&self.graph) {
            visited.insert(n);
            cost = cost.saturating_add(self.egraph.cost(self.graph.node_weight(n).unwrap()));
        }
        self.graph.retain_nodes(|_, x| visited.contains(&x));
        cost
    }
    fn traverse_class(&mut self, class: E::EClassId, pool: &Pool<E>) -> Option<(NodeIndex, usize)> {
        let mut nodes = pool.node_vec();
        self.egraph.expand_class(&class, &mut nodes);
        nodes
            .drain(..)
            .filter_map(|node| self.traverse_node(node, pool))
            .min_by_key(|(_, cost)| *cost)
    }

    fn traverse_node(&mut self, node: E::ENodeId, pool: &Pool<E>) -> Option<(NodeIndex, usize)> {
        match self.hashcons.get(&node) {
            Some(None) => {
                // This is a cycle (or points to one)
                return None;
            }
            Some(x) => {
                return *x;
            }
            None => {}
        };
        self.hashcons.insert(node.clone(), None);
        let mut classes = pool.class_vec();
        self.egraph.get_children(&node, &mut classes);
        let mut total_cost = self.egraph.cost(&node);
        let new_node = self.graph.add_node(node.clone());
        for class in classes.drain(..) {
            let (child, cost) = self.traverse_class(class, pool)?;
            self.graph.add_edge(new_node, child, ());
            total_cost = total_cost.saturating_add(cost);
        }
        let res = Some((new_node, total_cost));
        self.hashcons.insert(node, res);

        res
    }
}

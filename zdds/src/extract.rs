//! Routines for extracting DAGs of ENodes from an EGraph.
use std::hash::Hash;

use petgraph::{prelude::NodeIndex, visit::Dfs, Directed, Graph};

use crate::{choose_nodes, egraph::Pool, Egraph, HashMap, HashSet, Report};

/// The type used to return DAGs of expressions during extraction.
///
/// This is just a type alias for the underlying petgraph type, which is a
/// general graph rather than an acylic one.
pub type Dag<T> = Graph<T, (), Directed>;

/// The output "term" returned by an extaction procedure, represented as a
/// graph.
pub struct ExtractResult<T> {
    pub root: NodeIndex,
    pub dag: Dag<T>,
    pub total_cost: usize,
}

pub fn extract_greedy<E: Egraph>(
    egraph: &mut E,
    root: E::EClassId,
) -> Option<ExtractResult<E::ENodeId>> {
    extract(egraph, root, NullFilter)
}

pub fn extract_zdd<E: Egraph>(
    egraph: &mut E,
    root: E::EClassId,
    node_limit: Option<usize>,
) -> Option<(ExtractResult<E::ENodeId>, Report)> {
    let mut report = Report::default();
    let (nodes, _) = choose_nodes(egraph, root.clone(), Some(&mut report), node_limit)?;
    let extract_result = extract(egraph, root, SetFilter(nodes.iter().cloned().collect()))?;
    Some((extract_result, report))
}

pub(crate) fn extract<E: Egraph, F: ENodeFilter<E::ENodeId>>(
    egraph: &mut E,
    root: E::EClassId,
    filter: F,
) -> Option<ExtractResult<E::ENodeId>> {
    let mut extractor = Extractor {
        graph: Default::default(),
        hashcons: Default::default(),
        egraph,
        filter,
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

struct Extractor<'a, E: Egraph, Filter> {
    graph: Dag<E::ENodeId>,
    hashcons: HashMap<E::ENodeId, Option<(NodeIndex, usize)>>,
    egraph: &'a mut E,
    filter: Filter,
}

impl<'a, E: Egraph, Filter: ENodeFilter<E::ENodeId>> Extractor<'a, E, Filter> {
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
        self.filter.filter(&mut nodes);
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

pub(crate) trait ENodeFilter<T> {
    fn filter(&self, enodes: &mut Vec<T>);
}

pub(crate) struct NullFilter;

impl<T> ENodeFilter<T> for NullFilter {
    fn filter(&self, _: &mut Vec<T>) {}
}

pub(crate) struct SetFilter<T>(HashSet<T>);

impl<T: Eq + Hash> ENodeFilter<T> for SetFilter<T> {
    fn filter(&self, enodes: &mut Vec<T>) {
        enodes.retain(|node| self.0.contains(node))
    }
}

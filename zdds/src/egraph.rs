//! An abstraction for Egraphs and utilities for building ZDDs to represent
//! possible choices of ENodes.
use std::{
    cell::RefCell,
    fmt,
    hash::{BuildHasherDefault, Hash},
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
};

use hashbrown::{hash_map::Entry, HashMap};
use indexmap::IndexSet;
use rustc_hash::FxHasher;

use crate::{
    zdd::{NodeId, Report},
    HashSet, Zdd, ZddPool,
};

/// The `Egraph` trait encapsulates the core information required from an Egraph
/// to encode the extraction problem.
pub trait Egraph {
    type EClassId: Eq + Clone + Hash;
    type ENodeId: Eq + Clone + Hash;
    // Instead of returning into a vector, it'd be nice to return impl
    // Iterator<...>, but that is not stable yet.

    /// Optional printing routine: just for debugging purposes.
    fn print_node(&mut self, _node: &Self::ENodeId) -> String {
        Default::default()
    }

    /// For a given EClass, push all of its component ENodes into the `nodes` vector.
    fn expand_class(&mut self, class: &Self::EClassId, nodes: &mut Vec<Self::ENodeId>);
    /// For a given ENode, push all of its children into the `classes` vector.
    fn get_children(&mut self, node: &Self::ENodeId, classes: &mut Vec<Self::EClassId>);

    fn cost(&self, node: &Self::ENodeId) -> usize;
}

/// Given an Egraph, pick the minimum-cost set of enodes to be used during
/// extraction.
pub fn choose_nodes<E: Egraph>(
    egraph: &mut E,
    root: E::EClassId,
    report: Option<&mut Report>,
    node_limit: Option<usize>,
) -> Option<(Vec<E::ENodeId>, usize)> {
    let extractor = Extractor::new(root, egraph, node_limit);
    let (zdd_nodes, cost) = extractor.zdd.min_cost_set(|zdd_node| {
        if *zdd_node == INFINITY {
            usize::MAX
        } else {
            egraph.cost(
                extractor
                    .node_mapping
                    .get_index(zdd_node.index())
                    .expect("all nodes should be valid"),
            )
        }
    })?;
    let mut res = Vec::new();
    for node in zdd_nodes {
        // The only feasible solution had a cycle; bail out.
        if node == INFINITY {
            return None;
        }
        res.push(
            extractor
                .node_mapping
                .get_index(node.index())
                .unwrap()
                .clone(),
        );
    }
    if let Some(report) = report {
        const PRINT_META: bool = false;
        if PRINT_META {
            struct DisplayString(String);
            impl fmt::Debug for DisplayString {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "{}", self.0)
                }
            }
            extractor.zdd.for_each(|xs| {
                let to_print = Vec::from_iter(xs.iter().map(|x| {
                    DisplayString(if *x == INFINITY {
                        String::from("infinity")
                    } else {
                        egraph.print_node(extractor.node_mapping.get_index(x.index()).unwrap())
                    })
                }));
                eprintln!("{to_print:#?}");
            });
        }
        *report = extractor.zdd.report();
    }
    Some((res, cost))
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct ZddNode(u32);

const INFINITY: ZddNode = ZddNode(u32::MAX);

impl ZddNode {
    fn new(u: usize) -> ZddNode {
        assert!(u < u32::MAX as usize);
        ZddNode(u as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

pub(crate) struct Extractor<E: Egraph> {
    /// Assigns each e-node to its offset in the IndexSet. We want to assign our
    /// own offsets because (heuristically) nodes given a topological order will
    /// compress better in the ZDD.
    node_mapping: IndexSet<E::ENodeId, BuildHasherDefault<FxHasher>>,
    /// The ZDD encoding all the possible choices of ENode.
    zdd: Zdd<ZddNode>,
    cycle: Zdd<ZddNode>,
    bot: Zdd<ZddNode>,
    visited_set: HashSet<NodeId>,
    node_limit: usize,
}

impl<E: Egraph> Extractor<E> {
    pub(crate) fn new(
        root: E::EClassId,
        egraph: &mut E,
        node_limit: Option<usize>,
    ) -> Extractor<E> {
        let mut visited = HashMap::default();
        let node_mapping = IndexSet::default();
        let pool = ZddPool::with_cache_size(1 << 25);
        let zdd = Zdd::with_pool(pool.clone());
        let cycle = Zdd::singleton(pool, INFINITY);
        let bot = zdd.clone();
        let pool = Pool::default();
        let mut res = Extractor {
            node_mapping,
            zdd,
            cycle,
            bot,
            visited_set: Default::default(),
            node_limit: node_limit.unwrap_or(usize::MAX),
        };
        let root = res.traverse(&mut visited, root, egraph, &pool);
        res.zdd = root;
        res
    }

    fn traverse(
        &mut self,
        visited: &mut HashMap<E::EClassId, Option<Zdd<ZddNode>>>,
        class: E::EClassId,
        egraph: &mut E,
        pool: &Pool<E>,
    ) -> Zdd<ZddNode> {
        // Visited acts as both a memo cache (for completed nodes) and a cycle
        // detection mechanism. Cycles in the graph show up when we've started
        // processing a node, but have not finished processing its children
        // before seeing it again. Nodes that we've started processing are
        // marked with `None`.
        match visited.entry(class.clone()) {
            Entry::Occupied(o) => {
                return if let Some(node) = o.get() {
                    node.clone()
                } else {
                    self.cycle.clone()
                };
            }
            Entry::Vacant(v) => v.insert(None),
        };
        let mut nodes = pool.node_vec();
        egraph.expand_class(&class, &mut nodes);
        if nodes.is_empty() {
            return self.bot.clone();
        }

        let start_nodes = self.zdd.pool().size();

        let mut outer_nodes = pool.zdd_vec();
        for node in nodes.drain(..) {
            let node_id = self.get_zdd_node(&node);
            let mut classes = pool.class_vec();
            egraph.get_children(&node, &mut classes);
            let mut inner_nodes = pool.zdd_vec();
            for class in classes.drain(..) {
                inner_nodes.push(self.traverse(visited, class, egraph, pool));
            }

            let mut composite = Zdd::singleton(self.zdd.pool().clone(), node_id);
            for node in inner_nodes.drain(..) {
                composite.join(&node);
            }
            outer_nodes.push(composite)
        }
        let mut composite = outer_nodes.pop().unwrap();
        for node in outer_nodes.drain(..) {
            composite.merge(&node);
        }
        let pool_delta = self.zdd.pool().size().saturating_sub(start_nodes);
        if pool_delta > self.node_limit
            && composite.count_nodes(&mut self.visited_set) > self.node_limit
        {
            composite.freeze();
        }
        *visited.get_mut(&class).unwrap() = Some(composite.clone());
        composite
    }

    fn get_zdd_node(&mut self, node: &E::ENodeId) -> ZddNode {
        if let Some(x) = self.node_mapping.get_index_of(node) {
            ZddNode::new(x)
        } else {
            let (offset, _) = self.node_mapping.insert_full(node.clone());
            ZddNode::new(offset)
        }
    }
}

pub(crate) struct Pool<E: Egraph> {
    classes: RefCell<Vec<Vec<E::EClassId>>>,
    nodes: RefCell<Vec<Vec<E::ENodeId>>>,
    zdds: RefCell<Vec<Vec<Zdd<ZddNode>>>>,
}

impl<E: Egraph> Default for Pool<E> {
    fn default() -> Pool<E> {
        Pool {
            classes: Default::default(),
            nodes: Default::default(),
            zdds: Default::default(),
        }
    }
}

impl<E: Egraph> Pool<E> {
    pub(crate) fn class_vec(&self) -> PoolRef<Vec<E::EClassId>> {
        let res = self.classes.borrow_mut().pop().unwrap_or_default();
        PoolRef {
            elt: ManuallyDrop::new(res),
            pool: &self.classes,
        }
    }
    pub(crate) fn node_vec(&self) -> PoolRef<Vec<E::ENodeId>> {
        let res = self.nodes.borrow_mut().pop().unwrap_or_default();
        PoolRef {
            elt: ManuallyDrop::new(res),
            pool: &self.nodes,
        }
    }
    fn zdd_vec(&self) -> PoolRef<Vec<Zdd<ZddNode>>> {
        let res = self.zdds.borrow_mut().pop().unwrap_or_default();
        PoolRef {
            elt: ManuallyDrop::new(res),
            pool: &self.zdds,
        }
    }
}

pub(crate) trait Clearable {
    fn clear(&mut self);
}

impl<T> Clearable for Vec<T> {
    fn clear(&mut self) {
        self.clear()
    }
}

pub(crate) struct PoolRef<'a, T: Clearable> {
    elt: ManuallyDrop<T>,
    pool: &'a RefCell<Vec<T>>,
}

impl<'a, T: Clearable> Deref for PoolRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.elt
    }
}

impl<'a, T: Clearable> DerefMut for PoolRef<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.elt
    }
}

impl<'a, T: Clearable> Drop for PoolRef<'a, T> {
    fn drop(&mut self) {
        self.elt.clear();
        let t = (&self.elt) as *const ManuallyDrop<T>;
        let elt = unsafe { ManuallyDrop::into_inner(t.read()) };
        self.pool.borrow_mut().push(elt);
    }
}

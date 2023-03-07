//! An abstraction for Egraphs and a ZDD-based extraction algorithm.
use std::{
    cell::RefCell,
    hash::Hash,
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
};

use hashbrown::{hash_map::Entry, HashMap};
use indexmap::IndexSet;

use crate::{Zdd, ZddPool};

/// The `Egraph` trait encapsulates the core information required from an Egraph
/// to encode the extraction problem.
pub trait Egraph {
    type EClassId: Eq + Clone + Hash;
    type ENodeId: Eq + Clone + Hash;
    // Instead of returning into a vector, it'd be nice to return impl
    // Iterator<...>, but that is not stable yet.

    /// For a given EClass, push all of its component ENodes into the `nodes` vector.
    fn expand_class(&self, class: &Self::EClassId, nodes: &mut Vec<Self::ENodeId>);
    /// For a given ENode, push all of its children into the `classes` vector.
    fn get_children(&self, node: &Self::ENodeId, classes: &mut Vec<Self::EClassId>);

    fn cost(&self, node: &Self::ENodeId) -> usize;
}

/// Given an Egraph, pick the minimum-cost set of enodes to be used during
/// extraction.
pub fn choose_nodes<E: Egraph>(egraph: &E, root: E::EClassId) -> Option<(Vec<E::ENodeId>, usize)> {
    let extractor = Extractor::new(root, egraph);
    let (zdd_nodes, cost) = extractor.zdd.min_cost_set(|zdd_node| {
        if *zdd_node == INFINITY {
            usize::MAX
        } else {
            egraph.cost(
                extractor
                    .node_mapping
                    .get_index(zdd_node.0)
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
        res.push(extractor.node_mapping.get_index(node.0).unwrap().clone());
    }
    Some((res, cost))
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ZddNode(usize);

const INFINITY: ZddNode = ZddNode(usize::MAX);

impl ZddNode {
    fn new(u: usize) -> ZddNode {
        assert!(u < usize::MAX);
        ZddNode(u)
    }
}

pub(crate) struct Extractor<E: Egraph> {
    /// Assigns each e-node to its offset in the IndexSet. We want to assign our
    /// own offsets because (heuristically) nodes given a topological order will
    /// compress better in the ZDD.
    node_mapping: IndexSet<E::ENodeId>,
    /// The ZDD encoding all the possible choices of ENode.
    zdd: Zdd<ZddNode>,
    cycle: Zdd<ZddNode>,
    bot: Zdd<ZddNode>,
}

impl<E: Egraph> Extractor<E> {
    pub(crate) fn new(root: E::EClassId, egraph: &E) -> Extractor<E> {
        let mut visited = HashMap::default();
        let node_mapping = IndexSet::default();
        let pool = ZddPool::with_cache_size(1 << 20);
        let zdd = Zdd::with_pool(pool.clone());
        let cycle = Zdd::singleton(pool, INFINITY);
        let bot = zdd.clone();
        let pool = Pool::default();
        let mut res = Extractor {
            node_mapping,
            zdd,
            cycle,
            bot,
        };
        let root = res.traverse(&mut visited, root, egraph, &pool);
        res.zdd = root;
        res
    }

    fn traverse(
        &mut self,
        visited: &mut HashMap<E::EClassId, Option<Zdd<ZddNode>>>,
        class: E::EClassId,
        egraph: &E,
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

struct Pool<E: Egraph> {
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
    fn class_vec(&self) -> PoolRef<Vec<E::EClassId>> {
        let res = self.classes.borrow_mut().pop().unwrap_or_default();
        PoolRef {
            elt: ManuallyDrop::new(res),
            pool: &self.classes,
        }
    }
    fn node_vec(&self) -> PoolRef<Vec<E::ENodeId>> {
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

trait Clearable {
    fn clear(&mut self);
}

impl<T> Clearable for Vec<T> {
    fn clear(&mut self) {
        self.clear()
    }
}

struct PoolRef<'a, T: Clearable> {
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

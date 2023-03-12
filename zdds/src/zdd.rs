//! The core ZDD implementation. This implementation currently only supports a
//! limited subset of operations.
use std::{
    cell::RefCell,
    cmp::Ordering,
    fmt,
    hash::{BuildHasherDefault, Hash},
    rc::Rc,
};

use crate::{fixed_cache::Cache, HashMap, HashSet};
use indexmap::IndexSet;
use rustc_hash::FxHasher;

/// A shared pool of nodes and caches used to speed up ZDD operations. Clones of
/// a pool yield a handle to the same underlying collection of nodes: Zdds can
/// only be composed or compared if they are stored within the same pool.
pub struct ZddPool<T>(Rc<RefCell<ZddPoolRep<T>>>);

impl<T> Clone for ZddPool<T> {
    fn clone(&self) -> ZddPool<T> {
        ZddPool(self.0.clone())
    }
}

impl<T> ZddPool<T> {
    pub fn with_cache_size(cache_size: usize) -> ZddPool<T> {
        ZddPool(Rc::new(RefCell::new(ZddPoolRep::with_cache_size(
            cache_size,
        ))))
    }
}

impl<T: Eq + Hash + Ord + Clone> ZddPool<T> {
    pub(crate) fn make_node(&self, item: T, lo: NodeId, hi: NodeId) -> NodeId {
        self.0.borrow_mut().make_node(item, lo, hi)
    }
}

pub(crate) struct ZddPoolRep<T> {
    nodes: IndexSet<Node<T>, BuildHasherDefault<FxHasher>>,
    cache: Cache<(NodeId, NodeId, Operation), NodeId>,
}

impl<T> ZddPoolRep<T> {
    pub(crate) fn with_cache_size(cache_size: usize) -> ZddPoolRep<T> {
        ZddPoolRep {
            nodes: Default::default(),
            cache: Cache::new(cache_size),
        }
    }
    fn get_node(&self, node: NodeId) -> &Node<T> {
        debug_assert_ne!(node, UNIT);
        debug_assert_ne!(node, BOT);
        self.nodes.get_index(node.index()).as_ref().unwrap()
    }
}

impl<T: Eq + Hash + Ord + Clone> ZddPoolRep<T> {
    pub(crate) fn make_node(&mut self, item: T, lo: NodeId, hi: NodeId) -> NodeId {
        let node = Node { item, lo, hi };
        if let Some(id) = self.nodes.get_index_of(&node) {
            return NodeId::new(id);
        }
        let (res, _) = self.nodes.insert_full(node);
        NodeId::new(res)
    }

    fn min_cost_set(
        &self,
        table: &mut BackChainTable<T>,
        memo: &mut HashMap<NodeId, Option<(LinkId, usize)>>,
        cost: &impl Fn(&T) -> usize,
        node: NodeId,
    ) -> Option<(LinkId, usize)> {
        if node == BOT {
            return None;
        }
        if node == UNIT {
            return Some((NIL, 0));
        }
        if let Some(x) = memo.get(&node) {
            return *x;
        }
        let res = {
            let rep = self.get_node(node);
            let lo_cost = self.min_cost_set(table, memo, cost, rep.lo);
            let hi_cost = self.min_cost_set(table, memo, cost, rep.hi);
            match (lo_cost, hi_cost) {
                (None, None) => None,
                (None, Some((chain, opt))) => Some((
                    table.cons(rep.item.clone(), chain),
                    opt.saturating_add(cost(&rep.item)),
                )),
                (Some(x), None) => Some(x),
                (Some((lo_chain, lo_cost)), Some((hi_chain, hi_cost))) => {
                    let total_hi_cost = hi_cost.saturating_add(cost(&rep.item));
                    if lo_cost <= total_hi_cost {
                        Some((lo_chain, lo_cost))
                    } else {
                        Some((table.cons(rep.item.clone(), hi_chain), total_hi_cost))
                    }
                }
            }
        };
        memo.insert(node, res);
        res
    }

    fn union_nodes(&mut self, l: NodeId, r: NodeId) -> NodeId {
        if l == r {
            return l;
        }
        if l == BOT {
            return r;
        }
        if r == BOT {
            return l;
        }
        if let Some(res) = self.cache.get(&(l, r, Operation::Union)) {
            return *res;
        }

        let res = if l == UNIT {
            // Unit goes on the right
            self.union_nodes(r, l)
        } else if r == UNIT {
            let l_node = self.get_node(l).clone();
            let lo = self.union_nodes(l_node.lo, UNIT);
            self.make_node(l_node.item, lo, l_node.hi)
        } else {
            let l_node = self.get_node(l);
            let r_node = self.get_node(r);

            match l_node.item.cmp(&r_node.item) {
                Ordering::Equal => {
                    let item = l_node.item.clone();
                    let l_hi = l_node.hi;
                    let r_hi = r_node.hi;
                    let l_lo = l_node.lo;
                    let r_lo = r_node.lo;
                    let hi = self.union_nodes(l_hi, r_hi);
                    let lo = self.union_nodes(l_lo, r_lo);
                    self.make_node(item, lo, hi)
                }
                Ordering::Less => {
                    // l < r
                    // We will take 'l' to be the root node. But because 'l' is
                    // less, nothing in 'r' will appear in it, so we will only
                    // merge 'r' with the lo node.
                    let node = l_node.clone();
                    let lo = self.union_nodes(node.lo, r);
                    self.make_node(node.item, lo, node.hi)
                }
                Ordering::Greater => return self.union_nodes(r, l),
            }
        };

        self.cache.set((l, r, Operation::Union), res);
        res
    }

    fn join_nodes(&mut self, l: NodeId, r: NodeId) -> NodeId {
        if l == BOT || r == BOT {
            return BOT;
        }
        if l == UNIT {
            return r;
        }
        if r == UNIT {
            return l;
        }

        if let Some(res) = self.cache.get(&(l, r, Operation::Join)) {
            return *res;
        }

        let res = {
            let l_node = self.get_node(l);
            let r_node = self.get_node(r);

            match l_node.item.cmp(&r_node.item) {
                Ordering::Equal => {
                    let item = l_node.item.clone();
                    let l_hi = l_node.hi;
                    let r_hi = r_node.hi;
                    let l_lo = l_node.lo;
                    let r_lo = r_node.lo;
                    // hi hi, hi lo, lo hi, will all be sets that contain 'item'
                    // lo lo will not.
                    let hi_hi = self.join_nodes(l_hi, r_hi);
                    let hi_lo = self.join_nodes(l_hi, r_lo);
                    let lo_hi = self.join_nodes(l_lo, r_hi);
                    let mut hi = self.union_nodes(hi_hi, hi_lo);
                    hi = self.union_nodes(hi, lo_hi);

                    let lo = self.join_nodes(l_lo, r_lo);
                    self.make_node(item, lo, hi)
                }
                Ordering::Less => {
                    // merging hi with r will correctly add l to everything there.
                    //
                    // merging lo with r will also do the correct thing?
                    let node = l_node.clone();
                    let hi = self.join_nodes(node.hi, r);
                    let lo = self.join_nodes(node.lo, r);
                    self.make_node(node.item, lo, hi)
                }
                Ordering::Greater => return self.join_nodes(r, l),
            }
        };

        self.cache.set((l, r, Operation::Join), res);
        res
    }

    fn intersect_nodes(&mut self, l: NodeId, r: NodeId) -> NodeId {
        if l == r {
            return l;
        }
        if l == BOT || r == BOT {
            return BOT;
        }
        if let Some(res) = self.cache.get(&(l, r, Operation::Intersection)) {
            return *res;
        }

        let res = if l == UNIT {
            // Unit goes on the right
            self.intersect_nodes(r, l)
        } else if r == UNIT {
            // UNIT does not contain the top node, so recur on the sets without
            // it.
            let lo = self.get_node(l).lo;
            self.intersect_nodes(lo, UNIT)
        } else {
            let l_node = self.get_node(l);
            let r_node = self.get_node(r);

            match l_node.item.cmp(&r_node.item) {
                Ordering::Equal => {
                    let item = l_node.item.clone();
                    let l_hi = l_node.hi;
                    let r_hi = r_node.hi;
                    let l_lo = l_node.lo;
                    let r_lo = r_node.lo;
                    let hi = self.intersect_nodes(l_hi, r_hi);
                    let lo = self.intersect_nodes(l_lo, r_lo);
                    self.make_node(item, lo, hi)
                }
                Ordering::Less => {
                    // l < r, so l does not appear in r. Continue by intersecting l.lo with r
                    self.intersect_nodes(l_node.lo, r)
                }
                Ordering::Greater => return self.intersect_nodes(r, l),
            }
        };

        self.cache.set((l, r, Operation::Intersection), res);
        res
    }

    fn for_each(&self, prefix: &mut Vec<T>, node: NodeId, f: &mut impl FnMut(&[T])) {
        if node == BOT {
            return;
        }
        if node == UNIT {
            f(prefix);
            return;
        }
        let node = self.get_node(node).clone();
        self.for_each(prefix, node.lo, f);
        prefix.push(node.item);
        self.for_each(prefix, node.hi, f);
        prefix.pop().unwrap();
    }

    fn merge_sorted_vals(
        &mut self,
        node: NodeId,
        vals: impl DoubleEndedIterator<Item = T>,
    ) -> NodeId {
        let mut hi = UNIT;
        for item in vals.rev() {
            hi = self.make_node(item, BOT, hi);
        }
        self.union_nodes(node, hi)
    }
    fn dfs(&self, node_id: NodeId, visited: &mut HashSet<NodeId>) {
        if !visited.insert(node_id) {
            return;
        }
        if node_id == BOT || node_id == UNIT {
            return;
        }
        let node = self.get_node(node_id);
        self.dfs(node.hi, visited);
        self.dfs(node.lo, visited);
    }
    fn universe_size(&self, node_id: NodeId, cache: &mut HashMap<NodeId, usize>) -> usize {
        if node_id == BOT {
            return 0;
        }

        if node_id == UNIT {
            return 1;
        }

        if let Some(cached) = cache.get(&node_id) {
            return *cached;
        }
        let node = self.get_node(node_id);
        let lo_cost = self.universe_size(node.lo, cache);
        let hi_cost = self.universe_size(node.hi, cache);
        let res = lo_cost.saturating_add(hi_cost);
        cache.insert(node_id, res);
        res
    }
}

pub struct Zdd<T> {
    pool: ZddPool<T>,
    root: NodeId,
}

impl<T> Clone for Zdd<T> {
    fn clone(&self) -> Zdd<T> {
        Zdd {
            pool: self.pool.clone(),
            root: self.root,
        }
    }
}

impl<T: Eq + Ord + Hash + Clone> Zdd<T> {
    pub fn pool(&self) -> &ZddPool<T> {
        &self.pool
    }

    pub fn report(&self) -> Report {
        let mut visited = HashSet::default();
        self.pool.0.borrow().dfs(self.root, &mut visited);
        let mut counts = HashMap::default();
        let universe_size = self.pool.0.borrow().universe_size(self.root, &mut counts);
        Report {
            zdd_size: visited.len(),
            cache_hit_ratio: self.pool.0.borrow().cache.hit_ratio(),
            cache_capacity: self.pool.0.borrow().cache.capacity(),
            universe_size,
            pool_size: self.pool.0.borrow().nodes.len(),
        }
    }

    pub fn with_pool(pool: ZddPool<T>) -> Zdd<T> {
        Zdd::new(pool, BOT)
    }
    pub fn singleton(pool: ZddPool<T>, item: T) -> Zdd<T> {
        let node = pool.make_node(item, BOT, UNIT);
        Zdd::new(pool, node)
    }
    pub(crate) fn new(pool: ZddPool<T>, root: NodeId) -> Zdd<T> {
        Zdd { pool, root }
    }

    pub fn min_cost_set(&self, cost: impl Fn(&T) -> usize) -> Option<(Vec<T>, usize)> {
        let mut table = BackChainTable::default();
        let mut memo = HashMap::default();
        let (elts, cost) = self
            .pool
            .0
            .borrow()
            .min_cost_set(&mut table, &mut memo, &cost, self.root)?;
        let mut res = Vec::new();
        table.for_each(elts, |x| res.push(x.clone()));
        Some((res, cost))
    }

    /// Add the set of itmes in `items`. `items` must be sorted and contain no
    /// duplicates.
    pub fn add(&mut self, items: Vec<T>) {
        assert!(
            items.windows(2).all(|x| x[0] < x[1]),
            "input vector must be sorted and contain no duplicates"
        );
        self.root = self
            .pool
            .0
            .borrow_mut()
            .merge_sorted_vals(self.root, items.into_iter());
    }

    /// Remove all members from the current set not present in `other`.
    pub fn intersect(&mut self, other: &Zdd<T>) {
        assert!(
            Rc::ptr_eq(&self.pool.0, &other.pool.0),
            "attempt to intersect two Zdds from different pools"
        );
        self.root = self
            .pool
            .0
            .borrow_mut()
            .intersect_nodes(self.root, other.root);
    }

    /// Add all members of `other` to the current set.
    pub fn merge(&mut self, other: &Zdd<T>) {
        assert!(
            Rc::ptr_eq(&self.pool.0, &other.pool.0),
            "attempt to intersect two Zdds from different pools"
        );
        self.root = self.pool.0.borrow_mut().union_nodes(self.root, other.root);
    }

    /// For each element _a_ in the current set add _a ∪ b_ for all _b_ in
    /// `other`.
    pub fn join(&mut self, other: &Zdd<T>) {
        assert!(
            Rc::ptr_eq(&self.pool.0, &other.pool.0),
            "attempt to join two Zdds from different pools"
        );
        self.root = self.pool.0.borrow_mut().join_nodes(self.root, other.root);
    }

    /// Iterate over the sets represented by the Zdd.
    ///
    /// This operation should more or less only be used for debugging: `f` can
    /// be called O(2^n) times for a ZDD of size O(n). As such, this method does
    /// not aim to be efficient in terms of copies for the underlying data.
    pub fn for_each(&self, mut f: impl FnMut(&[T])) {
        self.pool
            .0
            .borrow()
            .for_each(&mut vec![], self.root, &mut f)
    }
}

/// Debug information about the size of the ZDD in memory.
#[derive(Default)]
pub struct Report {
    pub zdd_size: usize,
    pub pool_size: usize,
    pub universe_size: usize,
    pub cache_hit_ratio: f64,
    pub cache_capacity: usize,
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "root ZDD has size of {} nodes, representing {} sets",
            self.zdd_size, self.universe_size
        )?;
        writeln!(f, "total ZDD pool has contains {} nodes", self.pool_size)?;
        writeln!(
            f,
            "ZDD operation cache capacity is {} slots, with a hit ratio of {}",
            self.cache_capacity, self.cache_hit_ratio
        )
    }
}

pub(crate) const BOT: NodeId = NodeId(!0 - 1);
pub(crate) const UNIT: NodeId = NodeId(!0);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) struct NodeId(u32);

impl NodeId {
    fn new(u: usize) -> NodeId {
        assert!(
            u <= u32::MAX as usize - 2,
            "attempt to create a NodeId that is too large: {u}"
        );
        NodeId(u as u32)
    }
    fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct Node<T> {
    item: T,
    hi: NodeId,
    lo: NodeId,
}

/// A particular operation performed on a ZDD.
#[derive(PartialEq, Eq, Hash)]
enum Operation {
    /// Return a ZDD containing all sets in either operand.
    Union,
    /// Return a ZDD containing all sets in both operands.
    Intersection,
    /// Return a ZDD containing a ∪ b for all a in the LHS and b in the RHS.
    Join,
}

struct BackChainTable<T> {
    nodes: Vec<Link<T>>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct LinkId(usize);

const NIL: LinkId = LinkId(usize::MAX);

impl<T> BackChainTable<T> {
    fn cons(&mut self, elt: T, next: LinkId) -> LinkId {
        let res = self.nodes.len();
        self.nodes.push(Link { elt, next });
        LinkId(res)
    }
    fn for_each(&self, mut link: LinkId, mut f: impl FnMut(&T)) {
        while link != NIL {
            let node = &self.nodes[link.0];
            f(&node.elt);
            link = node.next;
        }
    }
}

impl<T> Default for BackChainTable<T> {
    fn default() -> BackChainTable<T> {
        BackChainTable {
            nodes: Default::default(),
        }
    }
}

struct Link<T> {
    elt: T,
    next: LinkId,
}

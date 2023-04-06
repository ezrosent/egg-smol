//! The core ZDD implementation. This implementation currently only supports a
//! limited subset of operations.
use std::{
    cell::RefCell,
    cmp::{self, Ordering},
    fmt,
    hash::{BuildHasher, BuildHasherDefault, Hash},
    mem,
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
    pub fn size(&self) -> usize {
        self.0.borrow().nodes.len()
    }
}

impl<T: Eq + Hash + Ord + Clone> ZddPool<T> {
    pub(crate) fn make_node(&self, item: T, lo: NodeId, hi: NodeId) -> NodeId {
        self.0.borrow_mut().make_node(item, lo, hi)
    }
}

pub(crate) struct ZddPoolRep<T> {
    scratch: IndexSet<Node<Val<T>>, BuildHasherDefault<FxHasher>>,
    nodes: IndexSet<Node<Val<T>>, BuildHasherDefault<FxHasher>>,
    gc_at: usize,
    cache: Cache<(NodeId, NodeId, Operation), NodeId>,
}

impl<T> ZddPoolRep<T> {
    pub(crate) fn with_cache_size(cache_size: usize) -> ZddPoolRep<T> {
        ZddPoolRep {
            nodes: Default::default(),
            scratch: Default::default(),
            gc_at: 1 << 12,
            cache: Cache::new(cache_size),
        }
    }
    fn get_node(&self, node: NodeId) -> &Node<Val<T>> {
        debug_assert_ne!(node, UNIT);
        debug_assert_ne!(node, BOT);
        self.nodes.get_index(node.index()).as_ref().unwrap()
    }
}

fn make_node_with_set<T: Eq + Hash>(
    item: T,
    lo: NodeId,
    hi: NodeId,
    nodes: &mut IndexSet<Node<T>, impl BuildHasher>,
) -> NodeId {
    if hi == BOT {
        return lo;
    }
    let node = Node { item, lo, hi };
    if let Some(id) = nodes.get_index_of(&node) {
        return NodeId::new(id);
    }
    let (res, _) = nodes.insert_full(node);
    NodeId::new(res)
}

impl<T: Eq + Hash + Ord + Clone> ZddPoolRep<T> {
    fn frozen(&mut self, node: NodeId) -> NodeId {
        self.make_val_node(Val::Meta(node), BOT, UNIT)
    }
    pub(crate) fn make_node(&mut self, item: T, lo: NodeId, hi: NodeId) -> NodeId {
        self.make_val_node(Val::Base(item), lo, hi)
    }

    fn make_val_node(&mut self, item: Val<T>, lo: NodeId, hi: NodeId) -> NodeId {
        make_node_with_set(item, lo, hi, &mut self.nodes)
    }

    pub(crate) fn should_gc(&self) -> bool {
        self.nodes.len() >= self.gc_at
    }

    fn gc(&mut self, roots: impl IntoIterator<Item = NodeId>) -> HashMap<NodeId, NodeId> {
        let mut mapping = HashMap::default();
        for root in roots {
            self.gc_traverse(root, &mut mapping);
        }
        self.nodes.clear();
        mem::swap(&mut self.nodes, &mut self.scratch);
        self.cache
            .remap(|(l, r, _), _| match (mapping.get(l), mapping.get(r)) {
                (Some(x), Some(y)) => {
                    *l = *x;
                    *r = *y;
                    true
                }
                _ => false,
            });
        self.gc_at = cmp::max(16, self.nodes.len() * 2);
        mapping
    }

    fn gc_traverse(&mut self, node_id: NodeId, mapping: &mut HashMap<NodeId, NodeId>) -> NodeId {
        if node_id == BOT || node_id == UNIT {
            return node_id;
        }
        if let Some(res) = mapping.get(&node_id) {
            return *res;
        }

        // NB: we clone the live contents of the pool. We could avoid this with
        // a bit more work if we ever get a case for elements that hard to
        // clone.

        let Node { item, lo, hi } = self.get_node(node_id).clone();
        let new_hi = self.gc_traverse(hi, mapping);
        let new_lo = self.gc_traverse(lo, mapping);
        let res = match &item {
            Val::Base(_) => make_node_with_set(item, new_lo, new_hi, &mut self.scratch),
            Val::Meta(n) => {
                let new_meta = self.gc_traverse(*n, mapping);
                make_node_with_set(Val::Meta(new_meta), new_lo, new_hi, &mut self.scratch)
            }
        };
        mapping.insert(node_id, res);
        res
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
                (None, Some((chain, opt))) => match &rep.item {
                    Val::Base(t) => {
                        Some((table.cons(t.clone(), chain), opt.saturating_add(cost(t))))
                    }
                    Val::Meta(n) => {
                        let (inner_chain, inner_cost) = self.min_cost_set(table, memo, cost, *n)?;
                        Some((
                            table.merge(inner_chain, chain),
                            opt.saturating_add(inner_cost),
                        ))
                    }
                },
                (Some(x), None) => Some(x),
                (Some((lo_chain, lo_cost)), Some((hi_chain, hi_cost))) => match &rep.item {
                    Val::Base(t) => {
                        let total_hi_cost = hi_cost.saturating_add(cost(t));
                        if lo_cost <= total_hi_cost {
                            Some((lo_chain, lo_cost))
                        } else {
                            Some((table.cons(t.clone(), hi_chain), total_hi_cost))
                        }
                    }
                    Val::Meta(n) => {
                        if let Some((inner_chain, inner_cost)) =
                            self.min_cost_set(table, memo, cost, *n)
                        {
                            let total_hi_cost = hi_cost.saturating_add(inner_cost);
                            if lo_cost <= total_hi_cost {
                                Some((lo_chain, lo_cost))
                            } else {
                                Some((table.merge(inner_chain, hi_chain), total_hi_cost))
                            }
                        } else {
                            Some((lo_chain, lo_cost))
                        }
                    }
                },
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
            self.make_val_node(l_node.item, lo, l_node.hi)
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
                    self.make_val_node(item, lo, hi)
                }
                Ordering::Less => {
                    // l < r
                    // We will take 'l' to be the root node. But because 'l' is
                    // less, nothing in 'r' will appear in it, so we will only
                    // merge 'r' with the lo node.
                    let node = l_node.clone();
                    let lo = self.union_nodes(node.lo, r);
                    self.make_val_node(node.item, lo, node.hi)
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
                    self.make_val_node(item, lo, hi)
                }
                Ordering::Less => {
                    // merging hi with r will correctly add l to everything there.
                    //
                    // merging lo with r will also do the correct thing?
                    let node = l_node.clone();
                    let hi = self.join_nodes(node.hi, r);
                    let lo = self.join_nodes(node.lo, r);
                    self.make_val_node(node.item, lo, hi)
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
                    self.make_val_node(item, lo, hi)
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

    fn for_each(&self, prefix: &mut IndexSet<T>, node: NodeId, f: &mut impl FnMut(&[T])) {
        if node == BOT {
            return;
        }
        if node == UNIT {
            let elts = Vec::from_iter(prefix.iter().cloned());
            f(&elts);
            return;
        }
        let node = self.get_node(node).clone();
        self.for_each(prefix, node.lo, f);
        match &node.item {
            Val::Base(t) => {
                if prefix.insert(t.clone()) {
                    self.for_each(prefix, node.hi, f);
                    prefix.pop().unwrap();
                } else {
                    self.for_each(prefix, node.hi, f);
                }
            }
            Val::Meta(n) => {
                // This is very inefficient!
                let start = prefix.len();

                // Use a trait object to limit compiler recursion depth during
                // monomorphization. Trait objects can't borrow local variables,
                // hence the Rc<RefCell<...>> business.
                let prefixes = Rc::new(RefCell::new(Vec::new()));
                #[allow(clippy::type_complexity)]
                let mut collect_prefixes: Box<dyn FnMut(&[T])> = Box::new(|elts: &[T]| {
                    prefixes
                        .borrow_mut()
                        .push(IndexSet::from_iter(elts.iter().cloned()));
                });
                self.for_each(prefix, *n, &mut collect_prefixes);
                for prefix in prefixes.borrow_mut().iter_mut() {
                    self.for_each(prefix, node.hi, f)
                }
                prefix.truncate(start)
            }
        }
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
    fn mermaid_diagram(
        &self,
        node_id: NodeId,
        diagram: &mut MermaidDiagram,
        render: &mut impl FnMut(&T) -> String,
        visited: &mut HashMap<NodeId, String>,
    ) -> String {
        if node_id == BOT {
            return MermaidDiagram::bot();
        }
        if node_id == UNIT {
            return MermaidDiagram::top();
        }
        if let Some(id) = visited.get(&node_id) {
            return id.clone();
        }
        let node = self.get_node(node_id);
        let lo = self.mermaid_diagram(node.lo, diagram, render, visited);
        let hi = self.mermaid_diagram(node.hi, diagram, render, visited);
        let rendered = match &node.item {
            Val::Base(b) => render(b),
            Val::Meta(_) => "meta".into(),
        };
        let id = format!("{}", node_id.0);
        diagram.prelude.push(format!("{id}[\"{rendered}\"]"));
        diagram.nodes.push(((id.clone(), lo), (id.clone(), hi)));
        visited.insert(node_id, id.clone());
        id
    }
    fn universe_size(
        &self,
        node_id: NodeId,
        cache: &mut HashMap<NodeId, (usize, usize)>,
    ) -> (usize, usize) {
        if node_id == BOT {
            return (0, 0);
        }

        if node_id == UNIT {
            return (1, 1);
        }

        if let Some(cached) = cache.get(&node_id) {
            return *cached;
        }
        let node = self.get_node(node_id);
        let (lo_min, lo_max) = self.universe_size(node.lo, cache);
        let (hi_min, hi_max) = self.universe_size(node.hi, cache);
        let min = lo_min.saturating_add(hi_min);
        let res = match &node.item {
            Val::Base(_) => (min, lo_max.saturating_add(hi_max)),
            Val::Meta(n) => {
                let n = *n;
                let (_, max) = self.universe_size(n, cache);
                (min, lo_max.saturating_add(hi_max.saturating_mul(max)))
            }
        };
        cache.insert(node_id, res);
        res
    }
}

/// Run a GC pass on the underlying Zdd pool, preserving any nodes referenced by
/// the given Zdds.
///
/// * It is recommended to only call this function after confirming that
/// `should_gc` returns true. This allows the cost of repeated garbage
/// collection passes to be amortized across a large number of incremental
/// operations.
///
/// * All Zdds in `zdds` must reference the same underlying pool.
pub fn gc_zdds<'a, T>(zdds: &mut [&mut Zdd<T>])
where
    T: Eq + Ord + Hash + Clone + 'a,
{
    if zdds.is_empty() {
        return;
    }
    assert!(zdds[1..]
        .iter()
        .all(|x| Rc::ptr_eq(&x.pool.0, &zdds[0].pool.0)));

    let pool = zdds[0].pool().clone();

    let mapping = pool.0.borrow_mut().gc(zdds.iter().map(|x| x.root));
    for zdd in zdds {
        zdd.root = mapping[&zdd.root]
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
        let mut counts = HashMap::default();
        let (universe_size_min, universe_size_max) =
            self.pool.0.borrow().universe_size(self.root, &mut counts);
        Report {
            zdd_size: self.count_nodes(&mut Default::default()),
            cache_hit_ratio: self.pool.0.borrow().cache.hit_ratio(),
            cache_capacity: self.pool.0.borrow().cache.capacity(),
            universe_size_min,
            universe_size_max,
            pool_size: self.pool.size(),
        }
    }

    /// Count the number of unique nodes in the Zdd.
    ///
    /// This method consumes a set for storing visited nodes. This allows
    /// repeated calls to `count_nodes` to reuse allocations.
    pub(crate) fn count_nodes(&self, visited: &mut HashSet<NodeId>) -> usize {
        self.pool.0.borrow().dfs(self.root, visited);
        let res = visited.len();
        visited.clear();
        res
    }

    pub fn with_pool(pool: ZddPool<T>) -> Zdd<T> {
        Zdd::new(pool, BOT)
    }

    /// Whether or not the underlying ZDD pool could use a GC pass.
    ///
    /// The heuristic here only looks for growth of the underlying pool since
    /// the last GC pass.
    pub fn should_gc(&self) -> bool {
        self.pool.0.borrow().should_gc()
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

    /// Freeze the ZDD.
    ///
    /// ZDDs that are frozen are treated as "synthetic elements" in the ZDD.
    /// Algorithms like `merge` and `join` will not recur under the root node
    /// for the ZDD. This can greatly increase efficiency of the construction,
    /// at the cost of losing optimality for many of the cost-minimization
    /// functions.
    pub fn freeze(&mut self) {
        self.root = self.pool.0.borrow_mut().frozen(self.root);
    }

    /// Render a mermaid diagram representing the ZDD.
    ///
    /// This method is not terribly efficient, but it should be sufficient for
    /// producing diagrams for small ZDDs, particularly if they are below the
    /// node limit. Frozen nodes are not rendered.
    pub fn mermaid_diagram(&self, mut render_node: impl FnMut(&T) -> String) -> String {
        let mut diagram = MermaidDiagram::default();
        self.pool.0.borrow().mermaid_diagram(
            self.root,
            &mut diagram,
            &mut render_node,
            &mut Default::default(),
        );
        diagram.render()
    }

    /// Iterate over the sets represented by the Zdd.
    ///
    /// This operation should more or less only be used for debugging or
    /// testing: `f` can be called O(2^n) times for a ZDD of size O(n). As such,
    /// this method does not aim to be efficient in terms of copies for the
    /// underlying data.
    pub fn for_each(&self, mut f: impl FnMut(&[T])) {
        self.pool
            .0
            .borrow()
            .for_each(&mut Default::default(), self.root, &mut f)
    }
}

/// Debug information about the size of the ZDD in memory.
#[derive(Default)]
pub struct Report {
    pub zdd_size: usize,
    pub pool_size: usize,
    pub universe_size_min: usize,
    pub universe_size_max: usize,
    pub cache_hit_ratio: f64,
    pub cache_capacity: usize,
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "root ZDD has size of {} nodes, representing between {} and {} sets",
            self.zdd_size, self.universe_size_min, self.universe_size_max
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

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, PartialOrd, Ord)]
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

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct Node<T> {
    item: T,
    hi: NodeId,
    lo: NodeId,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Val<T> {
    Base(T),
    Meta(NodeId),
}

impl<T: PartialOrd> PartialOrd for Val<T> {
    fn partial_cmp(&self, other: &Val<T>) -> Option<Ordering> {
        match (self, other) {
            (Val::Base(l), Val::Base(r)) => l.partial_cmp(r),
            (Val::Base(_), Val::Meta(_)) => Some(Ordering::Less),
            (Val::Meta(_), Val::Base(_)) => Some(Ordering::Greater),
            (Val::Meta(n1), Val::Meta(n2)) => n1.partial_cmp(n2),
        }
    }
}

impl<T: Ord> Ord for Val<T> {
    fn cmp(&self, other: &Val<T>) -> Ordering {
        match (self, other) {
            (Val::Base(l), Val::Base(r)) => l.cmp(r),
            (Val::Base(_), Val::Meta(_)) => Ordering::Less,
            (Val::Meta(_), Val::Base(_)) => Ordering::Greater,
            (Val::Meta(n1), Val::Meta(n2)) => n1.cmp(n2),
        }
    }
}

// TODO: replace item: T with item Either<T, NodeId>. Metanodes compare _larger_
// than any t (and then compare numerically).
// Replace a node with a metanode singleton during "GC" if its transitive size
// is large enough.
// During traversal (i.e. DAG construction) ... well we still need to figure
// that bit out.
// * We can compute a min-cost set. But now we may not have a mapping
// eclass => enode. During traversal we need to resolve conflicts, perhaps using
// greedy? That may not be sufficient though... Basically we need to build all
// sub-dags, but I think this is still a variant of the greedy algorithm. We
// essentially are using the ZDDs as a filter for which e-nodes are relevant in
// each class, then doing a greedy optimization from there.
//
// There's probably a way to share code with greedy here... just pass a filter.

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

impl<T: Hash + Eq> BackChainTable<T> {
    fn cons(&mut self, elt: T, next: LinkId) -> LinkId {
        let res = self.nodes.len();
        self.nodes.push(Link::Cons { elt, next });
        LinkId(res)
    }
    fn merge(&mut self, l: LinkId, r: LinkId) -> LinkId {
        let res = self.nodes.len();
        self.nodes.push(Link::Union { l, r });
        LinkId(res)
    }
    fn for_each(&self, link: LinkId, mut f: impl FnMut(&T)) {
        let mut seen = HashSet::default();
        let mut deferred = vec![link];
        while let Some(mut link) = deferred.pop() {
            while link != NIL {
                let node = &self.nodes[link.0];
                match &node {
                    Link::Cons { elt, next } => {
                        if seen.insert(elt) {
                            f(elt);
                        }
                        link = *next;
                    }
                    Link::Union { l, r } => {
                        link = *l;
                        deferred.push(*r);
                    }
                }
            }
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

enum Link<T> {
    Cons { elt: T, next: LinkId },
    Union { l: LinkId, r: LinkId },
}

type Edge = (String, String);
struct MermaidDiagram {
    prelude: Vec<String>,
    nodes: Vec<(Edge, Edge)>,
}

impl Default for MermaidDiagram {
    fn default() -> MermaidDiagram {
        MermaidDiagram {
            prelude: vec!["TOP[\"#8868;\"]".into(), "BOT[\"#8869;\"]".into()],
            nodes: vec![],
        }
    }
}

impl MermaidDiagram {
    fn bot() -> String {
        "BOT".into()
    }
    fn top() -> String {
        "TOP".into()
    }
    fn render(&self) -> String {
        let mut res: String = "flowchart TB\n".into();
        for decl in &self.prelude {
            res.push('\t');
            res.push_str(decl);
            res.push('\n');
        }
        for (lo, hi) in &self.nodes {
            res.push('\t');
            res.push_str(&format!("{} -.-> {}", lo.0, lo.1));
            res.push('\n');
            res.push('\t');
            res.push_str(&format!("{} ---> {}", hi.0, hi.1));
            res.push('\n');
        }
        res
    }
}

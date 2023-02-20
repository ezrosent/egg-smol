//! Interior nodes for the trie.

use std::{
    fmt::Debug,
    hash::{BuildHasher, Hash, Hasher},
    mem,
    rc::Rc,
};

trait Radix {
    const BITS: usize;
    const ARITY: usize = 1 << Self::BITS;
    fn round_down(k: usize) -> usize {
        (k / Self::BITS) * Self::BITS
    }
}

struct Radix5;
impl Radix for Radix5 {
    const BITS: usize = 5;
}

struct Radix4;
impl Radix for Radix4 {
    const BITS: usize = 4;
}

// NB: with generic constants we can parameterize the entire node by its radix.
// For now, we just keep 4 and 5 around and swap them out manually to
// test/validate assumptions. (e.g. Radix 4 leads to a deeper trie, but
// round_down is going to be faster).
type R = Radix5;

#[derive(Clone, Debug)]
pub(crate) enum Child<T> {
    Inner(Rc<Node<T>>),
    Leaf(T),
    Null,
}

impl<T: Item + PartialEq> PartialEq for Child<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Child::Inner(l), Child::Inner(r)) => Rc::ptr_eq(l, r) || l == r,
            (Child::Leaf(l), Child::Leaf(r)) => l == r,
            (Child::Null, Child::Null) => true,
            _ => false,
        }
    }
}

impl<T> Child<T> {
    pub(crate) fn for_each(&self, f: &mut impl FnMut(&T)) {
        match self {
            Child::Inner(n) => n.for_each(f),
            Child::Leaf(l) => f(l),
            Child::Null => {}
        }
    }
}

impl<T: Item + Eq> Eq for Child<T> {}

impl<T: Item + Clone> Child<T> {
    pub(crate) fn mutate(
        &mut self,
        key: u64,
        bits: usize,
        build_hasher: &impl BuildHasher,
        // if modify returns true, then the modified 't' is removed from the
        // tree and returned.
        modify: &mut impl FnMut(&mut T) -> bool,
    ) -> Option<T> {
        match self {
            Child::Inner(i) => {
                let res = i.mutate(key, bits, build_hasher, modify);
                if !i.bitset.has_one_element() {
                    return res;
                }
                // We've gone from 2 children to 1 at this node: we can inline
                // that child here, but we need to take special care to update
                // prefixes accordingly if this was a node in the "middle" of
                // the tree.
                let last = i.bitset.get_min();
                let prev_prefix = i.prefix();
                let prev_len = i.prefix_len();
                *self = mem::take(&mut Rc::make_mut(i).children[last]);
                if let Child::Inner(n) = self {
                    Rc::make_mut(n).prepend_prefix(prev_prefix, prev_len);
                }
                res
            }
            Child::Leaf(l) => {
                if !modify(l) {
                    return None;
                }
                if let Child::Leaf(l) = mem::take(self) {
                    Some(l)
                } else {
                    unreachable!()
                }
            }
            Child::Null => None,
        }
    }
}

impl<T: Item> Hash for Child<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Child::Inner(n) => {
                n.hash().hash(state);
                n.prefix().hash(state);
            }
            Child::Leaf(l) => l.key().hash(state),
            Child::Null => {}
        }
    }
}

impl<T> Default for Child<T> {
    fn default() -> Self {
        Child::Null
    }
}

// TODO:
// * double the size of the bitset, store discriminants in there.
// * prefix compression may be more trouble than its worth, let's keep lazy
// expansion but nix prefixes for now. Build new node representation before
// killing the prefixes so we can track the lookup degradation.
// * I suspect inserts are going to be so much slower though that it doesn't
// matter.

#[derive(Clone, Debug)]
pub(crate) struct Node<T> {
    prefix: u64,
    prefix_len: u32,
    hash: u32,
    bitset: Bitset,
    children: [Child<T>; R::ARITY],
}

impl<T> Default for Node<T> {
    fn default() -> Node<T> {
        Node {
            prefix: Default::default(),
            prefix_len: Default::default(),
            hash: Default::default(),
            bitset: Default::default(),
            children: Default::default(),
        }
    }
}

impl<T: Item + PartialEq> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.hash() != other.hash() {
            return false;
        }
        if self.prefix != other.prefix {
            return false;
        }
        if self.bitset != other.bitset {
            return false;
        }
        self.children
            .iter()
            .zip(other.children.iter())
            .all(|(l, r)| l == r)
    }
}

impl<T: Item + Eq> Eq for Node<T> {}

fn matching_prefix(l: u64, r: u64) -> usize {
    (l ^ r).leading_zeros() as usize
}

impl<T> Node<T> {
    fn new(prefix: u64, prefix_len: u32) -> Node<T> {
        debug_assert_eq!(prefix, truncate(prefix, prefix_len as usize));
        Node {
            prefix,
            prefix_len,
            hash: 0,
            bitset: Default::default(),
            children: Default::default(),
        }
    }

    fn for_each(&self, f: &mut impl FnMut(&T)) {
        self.children.iter().for_each(|c| c.for_each(f))
    }

    fn consume_prefix(&mut self, bits: usize) {
        debug_assert!(bits <= self.prefix_len());
        debug_assert_eq!(bits % R::BITS, 0);
        let bits = bits as u32;
        self.prefix <<= bits;
        self.prefix_len -= bits;
    }
    fn prefix(&self) -> u64 {
        debug_assert_eq!(self.prefix, truncate(self.prefix, self.prefix_len()));
        self.prefix
    }
    fn prefix_matches(&self, key: u64) -> bool {
        // prefixes start with the MSB
        matching_prefix(self.prefix(), key) >= self.prefix_len()
    }
    fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }
    fn prepend_prefix(&mut self, other: u64, bits: usize) {
        debug_assert!(bits + self.prefix_len() < 64);
        debug_assert_eq!(bits % R::BITS, 0);
        debug_assert_eq!(self.prefix, truncate(self.prefix, self.prefix_len()));
        debug_assert_eq!(other, truncate(other, bits));
        let bits = bits as u32;

        self.prefix = other | self.prefix >> bits;
        self.prefix_len += bits;
        debug_assert_eq!(self.prefix, truncate(self.prefix, self.prefix_len()));
    }
    fn hash(&self) -> u32 {
        self.hash
    }
}

fn truncate(prefix: u64, len: usize) -> u64 {
    if len == 0 {
        0
    } else {
        prefix & (!0u64).wrapping_shl(64 - len as u32)
    }
}

/// Given two items, compute an interior node containing them. 'bits' is a
/// cursor indicating the level of the tree where the leaves are being added.
pub(crate) fn merge_leaves<T: Item + Clone>(
    t1: T,
    t2: T,
    bits: usize,
    node: &mut Node<T>,
    h: &mut impl Hasher,
) {
    let k1 = t1.key();
    let k2 = t2.key();

    debug_assert_eq!(node.bitset.len(), 0);
    debug_assert_ne!(k1, k2);
    debug_assert_ne!(k1 << bits, k2 << bits);

    let bits = bits as u32;
    let shifted_1 = k1 << bits;
    let shifted_2 = k2 << bits;
    let prefix_len = R::round_down(matching_prefix(shifted_1, shifted_2));
    let prefix = truncate(shifted_1, prefix_len);

    debug_assert_eq!(prefix, truncate(shifted_2, prefix_len));

    node.prefix = prefix;
    node.prefix_len = prefix_len as u32;

    let next_k1 = next_node(shifted_1, prefix_len);
    let next_k2 = next_node(shifted_2, prefix_len);

    node.children[next_k1] = Child::Leaf(t1);
    node.children[next_k2] = Child::Leaf(t2);
    node.update_hash(h)
}

impl<T: Item + Clone> Node<T> {
    fn update_hash(&mut self, h: &mut impl Hasher) {
        self.bitset.clear();
        for (i, child) in self.children.iter().enumerate() {
            child.hash(h);
            if matches!(child, Child::Inner(_) | Child::Leaf(_)) {
                self.bitset.set(i);
            }
            self.bitset.set(i)
        }
        self.hash = h.finish() as u32;
    }
    pub(crate) fn mutate(
        self: &mut Rc<Self>,
        key: u64,
        mut bits: usize,
        build_hasher: &impl BuildHasher,
        // if modify returns true, then the modified 't' is removed from the
        // tree and returned.
        modify: &mut impl FnMut(&mut T) -> bool,
    ) -> Option<T> {
        let cur = key << bits;
        if !self.prefix_matches(cur) {
            return None;
        }
        bits += self.prefix_len();
        let slf = Rc::make_mut(self);
        let res =
            slf.children[next_node(key, bits)].mutate(key, bits + R::BITS, build_hasher, modify);
        slf.update_hash(&mut build_hasher.build_hasher());
        res
    }

    pub(crate) fn lookup(&self, key: u64, mut bits: usize) -> Option<&T> {
        debug_assert!(
            bits + self.prefix_len() < 64,
            "bits={bits}, prefix_len={}",
            self.prefix_len()
        );
        let cur = key << bits;
        if !self.prefix_matches(cur) {
            return None;
        }
        bits += self.prefix_len();
        match &self.children[next_node(key, bits)] {
            Child::Inner(node) => node.lookup_internal(key, bits + R::BITS),
            Child::Leaf(elt) => Some(elt),
            Child::Null => None,
        }
    }

    fn lookup_internal(&self, key: u64, mut bits: usize) -> Option<&T> {
        debug_assert!(
            bits + self.prefix_len() < 64,
            "bits={bits}, prefix_len={}",
            self.prefix_len()
        );
        bits += self.prefix_len();
        match &self.children[next_node(key, bits)] {
            Child::Inner(node) => node.lookup_internal(key, bits + R::BITS),
            Child::Leaf(elt) => Some(elt),
            Child::Null => None,
        }
    }

    pub(crate) fn insert(
        self: &mut Rc<Self>,
        key: u64,
        mut bits: usize,
        build_hasher: &impl BuildHasher,
        // TODO: make this FnOnce(Option<T>) -> T
        on_merge: impl FnOnce(Option<&T>) -> T,
    ) {
        let cur = key << bits;
        let matching = matching_prefix(self.prefix(), cur);
        if matching >= self.prefix_len() {
            bits += self.prefix_len();
            let slf = Rc::make_mut(self);
            let next = next_node(key, bits);
            match &mut slf.children[next] {
                Child::Inner(node) => {
                    // Interior node: continue the search.
                    node.insert(key, bits + R::BITS, build_hasher, on_merge);
                }
                Child::Leaf(l) if l.key() == key => {
                    // We've hit a leaf that matches. Go for the merge!
                    *l = on_merge(Some(l));
                }
                x @ Child::Leaf(_) => {
                    // We have a leaf that does not match. We need to compute
                    // the shared prefix and insert a new interior node with the
                    // current leaf and the new leaf as children.

                    // First: make the borrow checker happy. Swap in a
                    // placeholder interior node and extract the child out along
                    // with a mutable reference to that node.
                    let prev = mem::replace(x, Child::Inner(Rc::new(Node::default())));
                    let l = if let Child::Leaf(leaf) = prev {
                        leaf
                    } else {
                        unreachable!()
                    };
                    let new = if let Child::Inner(x) = x {
                        Rc::make_mut(x)
                    } else {
                        unreachable!()
                    };

                    bits += R::BITS;
                    merge_leaves(
                        l,
                        on_merge(None),
                        bits,
                        new,
                        &mut build_hasher.build_hasher(),
                    );
                }
                x @ Child::Null => {
                    let elt = on_merge(None);
                    *x = Child::Leaf(elt);
                }
            }
            slf.update_hash(&mut build_hasher.build_hasher());
            return;
        }

        // We need to split the prefix: we share 'matching' with the current keys
        let matching = R::round_down(matching);
        let mut new = Node::new(truncate(self.prefix(), matching), matching as u32);
        let l_child = next_node(key, bits + matching);
        new.children[l_child] = Child::Leaf(on_merge(None));

        debug_assert!(self.prefix_len() - matching >= R::BITS);
        let slf = Rc::make_mut(self);
        slf.consume_prefix(matching);
        let child_index = next_node(slf.prefix(), 0);
        slf.consume_prefix(R::BITS);
        new.children[child_index] = Child::Inner(self.clone());
        new.update_hash(&mut build_hasher.build_hasher());
        *self = Rc::new(new);
    }
}

#[inline(always)]
fn next_node(key: u64, bits: usize) -> usize {
    const OFFSET: usize = 64 - R::BITS;
    ((key << bits) >> OFFSET) as usize
}

pub(crate) trait Item {
    fn key(&self) -> u64;
}

#[repr(transparent)]
#[derive(Copy, Clone, Default, PartialEq, Eq, Debug)]
struct Bitset(u32);
const MAX_CHILDREN: usize = mem::size_of::<Bitset>() * 8;

impl Bitset {
    fn clear(&mut self) {
        self.0 = 0;
    }

    /// The number of set bits.
    fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    fn has_one_element(&self) -> bool {
        self.0.is_power_of_two()
    }

    /// Set 'bit'. The behavior is unspecified if 'bit' is out of range.
    fn set(&mut self, bit: usize) {
        debug_assert!(bit < MAX_CHILDREN);
        self.0 |= 1u32.wrapping_shl(bit as u32);
    }

    /// Get the minimum set bit. The behavior is unspecified if the set is empty.
    fn get_min(&self) -> usize {
        self.0.trailing_zeros() as usize
    }
}

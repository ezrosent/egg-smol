use std::{
    fmt,
    hash::{Hash, Hasher},
    mem::{self, ManuallyDrop, MaybeUninit},
    rc::Rc,
};

use rustc_hash::FxHasher;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u32)]
enum Kind {
    Null = 0,
    Leaf = 1,
    Collision = 2,
    Inner = 3,
}

const BITS: usize = 5;
const ARITY: usize = 1 << BITS;
type HashBits = u32;

pub(crate) trait HashItem: Clone {
    type Key: Eq + Hash;
    fn key(&self) -> &Self::Key;
}

pub(crate) struct Chunk<T> {
    bs: u64,
    hash: HashBits,
    len: u32,
    children: MaybeUninit<[Child<T>; ARITY]>,
}

type Leaf<T> = (T, HashBits);

union Child<T> {
    inner: ManuallyDrop<Rc<Chunk<T>>>,
    leaf: ManuallyDrop<Leaf<T>>,
    collision: ManuallyDrop<CollisionNode<T>>,
}

#[derive(Clone, PartialEq, Eq)]
struct CollisionNode<T> {
    hash: HashBits,
    data: Vec<T>,
}

// TODO: hash table, hash set implementation
// TODO: comments
// TODO: insertion benchmarks
// TODO: reevaluate whether to recompute hashes for leaf / collisions

impl<T: HashItem> Chunk<T> {
    pub(crate) fn for_each(&self, mut f: &mut impl FnMut(&T)) {
        for child in 0..ARITY {
            match self.get_kind(child) {
                Kind::Null => {}
                Kind::Leaf => f(&self.get_leaf(child).0),
                Kind::Collision => {
                    let collision = self.get_collision(child);
                    collision.data.iter().for_each(&mut f);
                }
                Kind::Inner => {
                    let inner = self.get_inner(child);
                    inner.for_each(f)
                }
            }
        }
    }

    pub(crate) fn get(&self, key: &T::Key, hash: u32, bits: u32) -> Option<&T> {
        let child = Self::mask(hash, bits);
        match self.get_kind(child) {
            Kind::Null => None,
            Kind::Leaf => {
                let (candidate, _) = self.get_leaf(child);
                if candidate.key() == key {
                    Some(candidate)
                } else {
                    None
                }
            }
            Kind::Collision => {
                let collision = self.get_collision(child);
                if collision.hash != hash {
                    None
                } else {
                    collision.data.iter().find(|x| x.key() == key)
                }
            }
            Kind::Inner => {
                let inner = self.get_inner(child);
                inner.get(key, hash, bits + BITS as u32)
            }
        }
    }

    pub(crate) fn insert(&mut self, mut elt: T, hash: u32, bits: u32) -> Option<T> {
        let child = Self::mask(hash, bits);
        match self.get_kind(child) {
            Kind::Null => {
                self.add_leaf(child, (elt, hash));
                None
            }
            Kind::Leaf => {
                let (candidate, h) = self.get_leaf(child);
                if elt.key() == candidate.key() {
                    self.with_leaf_mut(child, |(prev, _)| {
                        mem::swap(prev, &mut elt);
                    });
                    Some(elt)
                } else if *h == hash {
                    // we have a hash collision
                    self.replace_leaf_collision(child, |(prev, _)| CollisionNode {
                        hash,
                        data: vec![prev, elt],
                    });
                    None
                } else {
                    // We need to split this node: the hashes are distinct.
                    self.replace_leaf_chunk(child, |(other, other_hash)| {
                        let mut res = Chunk::default();
                        let next_bits = bits + BITS as u32;
                        res.insert(other, other_hash, next_bits);
                        res.insert(elt, hash, next_bits);
                        Rc::new(res)
                    });
                    None
                }
            }
            Kind::Collision => {
                let collision = self.get_collision(child);
                if collision.hash == hash {
                    // Another collision!
                    self.with_collision_mut(child, |c| {
                        if let Some(prev) = c.data.iter_mut().find(|x| x.key() == elt.key()) {
                            mem::swap(prev, &mut elt);
                            Some(elt)
                        } else {
                            c.data.push(elt);
                            None
                        }
                    })
                } else {
                    // Split this node and reinsert.
                    self.replace_collision_chunk(child, |c| {
                        let next_bits = bits + BITS as u32;
                        let next_child = Self::mask(c.hash, next_bits);
                        let mut res = Chunk::default();
                        res.add_collision(next_child, c);
                        res.insert(elt, hash, next_bits);
                        Rc::new(res)
                    });
                    None
                }
            }
            Kind::Inner => self.with_inner_mut(child, |inner| {
                Rc::make_mut(inner).insert(elt, hash, bits + BITS as u32)
            }),
        }
    }

    pub(crate) fn remove(&mut self, key: &T::Key, hash: u32, bits: u32) -> Option<T> {
        let child = Self::mask(hash, bits);
        match self.get_kind(child) {
            Kind::Null => None,
            Kind::Leaf => self
                .remove_leaf(child, |(leaf, _)| leaf.key() == key)
                .map(|(x, _)| x),
            Kind::Collision => {
                let collision = self.get_collision(child);
                if collision.hash != hash {
                    return None;
                }
                let to_remove = if let Some((i, _)) = collision
                    .data
                    .iter()
                    .enumerate()
                    .find(|(_, x)| x.key() == key)
                {
                    i
                } else {
                    return None;
                };

                if collision.data.len() == 2 {
                    // replace the collision with a leaf.
                    Some(self.replace_collision_leaf(child, |mut collision| {
                        let res = collision.data.swap_remove(to_remove);
                        let leaf = (collision.data.pop().unwrap(), collision.hash);
                        (res, leaf)
                    }))
                } else {
                    // Remove the element from the node
                    self.with_collision_mut(child, |collision| {
                        Some(collision.data.swap_remove(to_remove))
                    })
                }
            }
            Kind::Inner => {
                let (res, try_promote, bs) = self.with_inner_mut(child, |inner| {
                    let res = Rc::make_mut(inner).remove(key, hash, bits + BITS as u32);
                    (res, inner.len == 1, inner.bs)
                });
                if try_promote {
                    self.replace_chunk_with_child(child, bs.trailing_zeros() as usize / 2)
                }
                res
            }
        }
    }

    #[inline(always)]
    fn mask(hash: u32, bits: u32) -> usize {
        ((hash >> bits) % ARITY as u32) as usize
    }

    /// Remove the given hashcode from the node's digest.
    fn remove_hash(&mut self, hc: u32) {
        self.hash ^= hc;
    }

    /// Add the given hashcode to the node's digest.
    fn add_hash(&mut self, hc: u32) {
        self.hash ^= hc;
    }

    fn add_leaf(&mut self, i: usize, leaf: Leaf<T>) {
        assert_eq!(self.get_kind(i), Kind::Null);
        assert!(i < ARITY);
        unsafe {
            self.add_hash(leaf.1);
            self.child_ptr_mut(i).write(Child {
                leaf: ManuallyDrop::new(leaf),
            })
        }
        self.set_kind(i, Kind::Leaf);
        self.len += 1;
    }
    fn add_collision(&mut self, i: usize, collision: CollisionNode<T>) {
        assert_eq!(self.get_kind(i), Kind::Null);
        assert!(i < ARITY);
        unsafe {
            self.add_hash(collision.hash);
            self.child_ptr_mut(i).write(Child {
                collision: ManuallyDrop::new(collision),
            })
        }
        self.set_kind(i, Kind::Collision);
        self.len += 1;
    }

    fn replace_leaf_chunk(&mut self, i: usize, chunk: impl FnOnce(Leaf<T>) -> Rc<Chunk<T>>) {
        assert_eq!(self.get_kind(i), Kind::Leaf);
        assert!(i < ARITY);
        unsafe {
            let ptr = self.child_ptr_mut(i);
            let leaf = ManuallyDrop::into_inner(ptr.read().leaf);
            self.remove_hash(leaf.1);
            let inner = chunk(leaf);
            self.add_hash(inner.hash);
            ptr.write(Child {
                inner: ManuallyDrop::new(inner),
            });
        }
        self.set_kind(i, Kind::Inner);
    }

    fn replace_collision_chunk(
        &mut self,
        i: usize,
        chunk: impl FnOnce(CollisionNode<T>) -> Rc<Chunk<T>>,
    ) {
        assert_eq!(self.get_kind(i), Kind::Collision);
        assert!(i < ARITY);
        unsafe {
            let ptr = self.child_ptr_mut(i);
            let collision = ManuallyDrop::into_inner(ptr.read().collision);
            self.remove_hash(collision.hash);
            let inner = chunk(collision);
            self.add_hash(inner.hash);
            ptr.write(Child {
                inner: ManuallyDrop::new(inner),
            });
        }
        self.set_kind(i, Kind::Inner);
    }

    fn replace_collision_leaf<R>(
        &mut self,
        i: usize,
        leaf: impl FnOnce(CollisionNode<T>) -> (R, Leaf<T>),
    ) -> R {
        assert_eq!(self.get_kind(i), Kind::Collision);
        assert!(i < ARITY);
        unsafe {
            let ptr = self.child_ptr_mut(i);
            let collision = ManuallyDrop::into_inner(ptr.read().collision);
            self.remove_hash(collision.hash);
            let (res, leaf) = leaf(collision);
            self.add_hash(leaf.1);
            ptr.write(Child {
                leaf: ManuallyDrop::new(leaf),
            });
            self.set_kind(i, Kind::Leaf);
            res
        }
    }

    fn replace_chunk_with_child(&mut self, i: usize, child: usize) {
        assert_eq!(self.get_kind(i), Kind::Inner);
        unsafe {
            // First, check if the grandchild is another interior node. If it
            // is, stop: we can't collapse interior paths for this trie.
            let ptr = self.child_ptr_mut(i);
            let chunk_mut = &mut (&mut *ptr).inner;
            let grandchild_kind = chunk_mut.get_kind(child);
            if let Kind::Inner = grandchild_kind {
                // Abort!
                return;
            }

            // We have some kind of 'leaf': promote the grandchild.

            let mut chunk = ManuallyDrop::into_inner(ptr.read().inner);
            debug_assert_eq!(chunk.len, 1);
            let grandchild_kind = chunk.get_kind(child);
            let chunk_mut = Rc::make_mut(&mut chunk);
            let grandchild = chunk_mut.child_ptr_mut(child).read();
            // Null out the elements of `chunk`: we're going to drop it.
            chunk_mut.set_kind(child, Kind::Null);
            chunk_mut.len = 0;

            ptr.write(grandchild);
            self.set_kind(i, grandchild_kind);

            // Don't bother updating the hash: one-element chunks will have the
            // same hash as their children.
        }
    }

    fn replace_leaf_collision(
        &mut self,
        i: usize,
        collision: impl FnOnce(Leaf<T>) -> CollisionNode<T>,
    ) {
        assert_eq!(self.get_kind(i), Kind::Leaf);
        assert!(i < ARITY);
        unsafe {
            let ptr = self.child_ptr_mut(i);
            let leaf = ManuallyDrop::into_inner(ptr.read().leaf);
            self.remove_hash(leaf.1);
            let collision = collision(leaf);
            self.add_hash(collision.hash);
            ptr.write(Child {
                collision: ManuallyDrop::new(collision),
            });
        }
        self.set_kind(i, Kind::Collision);
    }

    // "setters" are CPS-d so we can properly adjust hashcodes.

    fn remove_leaf(&mut self, i: usize, f: impl FnOnce(&Leaf<T>) -> bool) -> Option<Leaf<T>> {
        assert_eq!(self.get_kind(i), Kind::Leaf);
        assert!(i < 32);
        unsafe {
            let ptr = self.child_ptr_mut(i);
            let leaf = &(&*ptr).leaf;
            if !f(leaf) {
                return None;
            }
            // remove

            // Borrow of `leaf` is over

            // Safe because remove_hash only touches the hash code
            self.remove_hash(leaf.1);
            self.len -= 1;
            self.set_kind(i, Kind::Null);
            // Safe because `ptr` is no longer reachable with Kind::Null.
            Some(ManuallyDrop::into_inner(ptr.read().leaf))
        }
    }

    fn with_leaf_mut<R>(&mut self, i: usize, f: impl FnOnce(&mut Leaf<T>) -> R) -> R {
        assert_eq!(self.get_kind(i), Kind::Leaf);
        assert!(i < 32);
        let leaf: &mut Leaf<T> = unsafe {
            let child = &mut *self.child_ptr_mut(i);
            &mut child.leaf
        };
        self.remove_hash(leaf.1);
        let res = f(leaf);
        self.add_hash(leaf.1);
        res
    }

    fn with_collision_mut<R>(&mut self, i: usize, f: impl FnOnce(&mut CollisionNode<T>) -> R) -> R {
        assert_eq!(self.get_kind(i), Kind::Collision);
        assert!(i < 32);
        let node: &mut CollisionNode<T> = unsafe {
            let child = &mut *self.child_ptr_mut(i);
            &mut child.collision
        };
        self.remove_hash(node.hash);
        let res = f(node);
        self.add_hash(node.hash);
        res
    }

    fn with_inner_mut<R>(&mut self, i: usize, f: impl FnOnce(&mut Rc<Chunk<T>>) -> R) -> R {
        assert_eq!(self.get_kind(i), Kind::Inner);
        assert!(i < 32);
        let node: &mut Rc<Chunk<T>> = unsafe {
            let child = &mut *self.child_ptr_mut(i);
            &mut child.inner
        };
        self.remove_hash(node.hash);
        let res = f(node);
        self.add_hash(node.hash);
        res
    }

    fn set_kind(&mut self, i: usize, k: Kind) {
        debug_assert!(i < 32);
        #[inline(always)]
        fn set_bit(bs: &mut u64, i: u32) {
            *bs |= 1 << i;
        }
        #[inline(always)]
        fn clear_bit(bs: &mut u64, i: u32) {
            *bs &= !(1 << i);
        }
        let i = i as u32;
        match k {
            Kind::Null => {
                debug_assert_eq!(k as u32, 0);
                clear_bit(&mut self.bs, 2 * i);
                clear_bit(&mut self.bs, 2 * i + 1);
            }
            Kind::Leaf => {
                debug_assert_eq!(k as u32, 1);
                set_bit(&mut self.bs, 2 * i);
                clear_bit(&mut self.bs, 2 * i + 1);
            }
            Kind::Collision => {
                debug_assert_eq!(k as u32, 2);
                clear_bit(&mut self.bs, 2 * i);
                set_bit(&mut self.bs, 2 * i + 1);
            }
            Kind::Inner => {
                debug_assert_eq!(k as u32, 3);
                set_bit(&mut self.bs, 2 * i);
                set_bit(&mut self.bs, 2 * i + 1);
            }
        }
        debug_assert_eq!(self.get_kind(i as usize), k);
    }
}

impl<T> Chunk<T> {
    fn get_kind(&self, i: usize) -> Kind {
        debug_assert!(i < 32);
        match (self.bs >> (i * 2)) % 4 {
            0 => Kind::Null,
            1 => Kind::Leaf,
            2 => Kind::Collision,
            3 => Kind::Inner,
            _ => unreachable!(),
        }
    }

    unsafe fn child_ptr(&self, i: usize) -> *const Child<T> {
        (self.children.as_ptr() as *const Child<T>).add(i)
    }

    unsafe fn child_ptr_mut(&mut self, i: usize) -> *mut Child<T> {
        (self.children.as_mut_ptr() as *mut Child<T>).add(i)
    }
    fn get_leaf(&self, i: usize) -> &(T, HashBits) {
        assert_eq!(self.get_kind(i), Kind::Leaf);
        assert!(i < ARITY);
        unsafe {
            let child = &*self.child_ptr(i);
            &child.leaf
        }
    }

    fn get_collision(&self, i: usize) -> &CollisionNode<T> {
        assert_eq!(self.get_kind(i), Kind::Collision);
        assert!(i < ARITY);
        unsafe {
            let child = &*self.child_ptr(i);
            &child.collision
        }
    }

    fn get_inner(&self, i: usize) -> &Rc<Chunk<T>> {
        assert_eq!(self.get_kind(i), Kind::Inner);
        assert!(i < ARITY);
        unsafe {
            let child = &*self.child_ptr(i);
            &child.inner
        }
    }
}

// -- trait implementations --

impl<T> Hash for Chunk<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}

impl<T> Default for Chunk<T> {
    fn default() -> Chunk<T> {
        Chunk {
            bs: 0,
            hash: 0,
            len: 0,
            children: MaybeUninit::uninit(),
        }
    }
}

impl<T: PartialEq> PartialEq for Chunk<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.hash != other.hash || self.bs != other.bs || self.len != other.len {
            return false;
        }
        for i in 0..ARITY {
            match self.get_kind(i) {
                Kind::Null => {}
                Kind::Leaf => {
                    if self.get_leaf(i) != other.get_leaf(i) {
                        return false;
                    }
                }
                Kind::Collision => {
                    if self.get_collision(i) != other.get_collision(i) {
                        return false;
                    }
                }
                Kind::Inner => {
                    let inner_l = self.get_inner(i);
                    let inner_r = other.get_inner(i);
                    if !Rc::ptr_eq(inner_l, inner_r) && inner_l != inner_r {
                        return false;
                    }
                }
            }
        }
        true
    }
}

impl<T: Clone> Clone for Chunk<T> {
    fn clone(&self) -> Chunk<T> {
        let mut res = Chunk {
            bs: self.bs,
            hash: self.hash,
            len: self.len,
            children: MaybeUninit::uninit(),
        };

        for i in 0..ARITY {
            let ptr = unsafe { res.child_ptr_mut(i) };
            let child = match self.get_kind(i) {
                Kind::Null => continue,
                Kind::Leaf => Child {
                    leaf: ManuallyDrop::new(self.get_leaf(i).clone()),
                },
                Kind::Collision => Child {
                    collision: ManuallyDrop::new(self.get_collision(i).clone()),
                },
                Kind::Inner => Child {
                    inner: ManuallyDrop::new(self.get_inner(i).clone()),
                },
            };
            unsafe { ptr.write(child) }
        }
        res
    }
}
impl<T: Eq> Eq for Chunk<T> {}

impl<T> Drop for Chunk<T> {
    fn drop(&mut self) {
        for i in 0..ARITY {
            if self.len == 0 {
                return;
            }
            match self.get_kind(i) {
                Kind::Null => continue,
                Kind::Leaf => unsafe {
                    let child = &mut *self.child_ptr_mut(i);
                    ManuallyDrop::drop(&mut child.leaf);
                },
                Kind::Collision => unsafe {
                    let child = &mut *self.child_ptr_mut(i);
                    ManuallyDrop::drop(&mut child.collision);
                },
                Kind::Inner => unsafe {
                    let child = &mut *self.child_ptr_mut(i);
                    ManuallyDrop::drop(&mut child.inner);
                },
            }
            self.len -= 1;
        }
    }
}

pub(crate) fn hash_value(k: &impl Hash) -> HashBits {
    let mut hasher = FxHasher::default();
    k.hash(&mut hasher);
    hasher.finish() as HashBits
}

impl<T: fmt::Debug> fmt::Debug for Chunk<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Chunk{{")?;
        write!(f, "len: {:?}, ", self.len)?;
        write!(f, "hash: {:?}, ", self.hash)?;
        write!(f, "bs: {:064b}, ", self.bs)?;
        writeln!(f, "children: [")?;
        for i in 0..ARITY {
            let is_last = i == ARITY - 1;
            let suffix = if is_last { "]" } else { ", " };
            match self.get_kind(i) {
                Kind::Null => write!(f, "Null{suffix}")?,
                Kind::Leaf => write!(f, "<{:?}>{suffix}", self.get_leaf(i))?,
                Kind::Collision => {
                    let collision = self.get_collision(i);
                    write!(
                        f,
                        "<hash:{:?}, {:?}>{suffix}",
                        collision.hash, &collision.data
                    )?;
                }
                Kind::Inner => {
                    write!(f, "{:?}{suffix}", self.get_inner(i))?;
                }
            }
        }
        write!(f, "}}")
    }
}

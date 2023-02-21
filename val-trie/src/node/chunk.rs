use std::{
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    mem::{ManuallyDrop, MaybeUninit},
    rc::Rc,
};

use rustc_hash::FxHasher;

use super::{Radix, R};

type H = BuildHasherDefault<FxHasher>;

pub(crate) struct Chunk<T> {
    bs: u64,
    hash: u64,
    children: MaybeUninit<[Child<T>; R::ARITY]>,
}

union Child<T> {
    ptr: ManuallyDrop<Rc<Chunk<T>>>,
    leaf: ManuallyDrop<T>,
}

impl<T> Default for Chunk<T> {
    fn default() -> Self {
        Chunk {
            bs: 0,
            hash: 0,
            children: MaybeUninit::uninit(),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) struct Kind(u32);

const NULL: Kind = Kind(0);
const LEAF: Kind = Kind(1);
const INNER: Kind = Kind(2);

fn hash_value(h: &impl Hash) -> u64 {
    let mut hasher = H::default().build_hasher();
    h.hash(&mut hasher);
    hasher.finish()
}

fn combine_hashes(x: u64, y: u64) -> u64 {
    x ^ y
}

fn remove_hash(summary: u64, to_remove: u64) -> u64 {
    summary ^ to_remove
}

// High-level operations:

impl<T: Hash + Clone> Chunk<T> {
    pub(crate) fn get(&self, key: u64, bits: usize) -> Option<&T> {
        let child = (key >> bits) as usize % R::ARITY;
        let k = self.kind(child);
        if k == NULL {
            return None;
        }
        if k == INNER {
            return unsafe { self.get_inner(child).get(key, bits + R::BITS) };
        }
        unsafe { Some(self.get_leaf(child)) }
    }

    pub(crate) fn insert(&mut self, key: u64, bits: usize, elt: T) {
        let please_remove_after_insert_is_more_general = 1;
        let child = (key >> bits) as usize % R::ARITY;
        let k = self.kind(child);
        if k == NULL {
            unsafe { self.set_leaf(child, elt) };
            return;
        }
        if k == INNER {
            unsafe {
                self.modify_chunk(child, |chunk| {
                    chunk.insert(key, bits + R::BITS, elt);
                })
            };
            return;
        }
        // Two leaves
        todo!()
    }
}

// Low-level / unsafe ops

impl<T> Chunk<T> {
    pub(crate) fn n_children(&self) -> usize {
        self.bs.count_ones() as usize
    }
    pub(crate) fn has_one_element(&self) -> bool {
        self.bs.is_power_of_two()
    }
    pub(crate) fn kind(&self, i: usize) -> Kind {
        debug_assert!(i <= R::ARITY);
        Kind(((self.bs >> (i * 2)) % 4) as u32)
    }

    pub(crate) unsafe fn get_leaf(&self, i: usize) -> &T {
        debug_assert_eq!(self.kind(i), LEAF);
        let child = &*self.child_ptr(i);
        &child.leaf
    }

    pub(crate) unsafe fn get_inner(&self, i: usize) -> &Rc<Chunk<T>> {
        debug_assert_eq!(self.kind(i), INNER);
        let child = &*self.child_ptr(i);
        &child.ptr
    }

    unsafe fn child_ptr(&self, i: usize) -> *mut Child<T> {
        debug_assert!(i < R::ARITY);
        (self.children.as_ptr() as *mut Child<T>).add(i)
    }
}

impl<T: Hash> Chunk<T> {
    pub(crate) fn set_kind(&mut self, i: usize, k: Kind) {
        self.bs |= (k.0 as u64) << (i * 2)
    }

    pub(crate) unsafe fn set_leaf(&mut self, i: usize, t: T) {
        debug_assert_eq!(self.kind(i), NULL);
        let hc = hash_value(&t);
        self.write_leaf(i, t);
        self.set_kind(i, LEAF);
        self.hash = combine_hashes(self.hash, hc);
    }

    unsafe fn write_leaf(&mut self, i: usize, t: T) {
        self.child_ptr(i).write(Child {
            leaf: ManuallyDrop::new(t),
        })
    }

    pub(crate) unsafe fn set_inner(&mut self, i: usize, chunk: Rc<Chunk<T>>) {
        debug_assert_eq!(self.kind(i), NULL);
        let hc = chunk.hash;
        self.write_chunk(i, chunk);
        self.set_kind(i, INNER);
        self.hash = combine_hashes(self.hash, hc);
    }

    unsafe fn write_chunk(&mut self, i: usize, chunk: Rc<Chunk<T>>) {
        self.child_ptr(i).write(Child {
            ptr: ManuallyDrop::new(chunk),
        })
    }

    pub(crate) unsafe fn replace_leaf_chunk(
        &mut self,
        i: usize,
        chunk: impl FnOnce(T) -> Rc<Chunk<T>>,
    ) {
        debug_assert_eq!(self.kind(i), LEAF);
        let child_ptr = self.child_ptr(i);
        let leaf_ptr: *mut ManuallyDrop<T> = &mut (*child_ptr).leaf;
        let leaf = leaf_ptr.read();
        self.hash = remove_hash(self.hash, hash_value(&leaf));
        let new = chunk(ManuallyDrop::into_inner(leaf));
        self.hash = combine_hashes(self.hash, new.hash);
        child_ptr.write(Child {
            ptr: ManuallyDrop::new(new),
        });
        self.set_kind(i, INNER);
    }

    pub(crate) unsafe fn replace_chunk_leaf(
        &mut self,
        i: usize,
        leaf: impl FnOnce(Rc<Chunk<T>>) -> T,
    ) {
        debug_assert_eq!(self.kind(i), INNER);
        let child_ptr = self.child_ptr(i);
        let chunk_ptr: *mut ManuallyDrop<Rc<Chunk<T>>> = &mut (*child_ptr).ptr;
        let chunk = chunk_ptr.read();
        self.hash = remove_hash(self.hash, chunk.hash);
        let new = leaf(ManuallyDrop::into_inner(chunk));
        self.hash = combine_hashes(self.hash, hash_value(&new));
        child_ptr.write(Child {
            leaf: ManuallyDrop::new(new),
        });
        self.set_kind(i, LEAF);
    }

    pub(crate) unsafe fn modify_leaf(&mut self, i: usize, modify: impl FnOnce(&mut T)) {
        debug_assert_eq!(self.kind(i), LEAF);
        let child_ptr = self.child_ptr(i);
        let leaf = &mut (*child_ptr).leaf;
        self.hash = remove_hash(self.hash, hash_value(leaf));
        modify(leaf);
        self.hash = combine_hashes(self.hash, hash_value(leaf));
    }

    pub(crate) unsafe fn remove_leaf(&mut self, i: usize) -> T {
        debug_assert_eq!(self.kind(i), LEAF);
        let child_ptr = self.child_ptr(i);
        let leaf = &mut (*child_ptr).leaf;
        self.hash = remove_hash(self.hash, hash_value(leaf));
        self.set_kind(i, NULL);
        ManuallyDrop::take(leaf)
    }
}

impl<T: Hash + Clone> Chunk<T> {
    pub(crate) unsafe fn modify_chunk(&mut self, i: usize, modify: impl FnOnce(&mut Chunk<T>)) {
        debug_assert_eq!(self.kind(i), INNER);
        let child_ptr = self.child_ptr(i);
        let chunk = Rc::make_mut(&mut (*child_ptr).ptr);
        self.hash = remove_hash(self.hash, chunk.hash);
        modify(chunk);
        self.hash = combine_hashes(self.hash, chunk.hash);
    }
}

impl<T> Hash for Chunk<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl<T: PartialEq> PartialEq for Chunk<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.bs != other.bs || self.hash != other.hash {
            return false;
        }
        for i in 0..R::ARITY {
            let kind = self.kind(i);
            if kind == NULL {
                continue;
            }

            unsafe {
                if kind == INNER {
                    let l = self.get_inner(i);
                    let r = other.get_inner(i);
                    let equal = Rc::ptr_eq(l, r) || l == r;
                    if !equal {
                        return false;
                    }
                }

                if kind == LEAF {
                    let l = self.get_leaf(i);
                    let r = self.get_leaf(i);
                    if l != r {
                        return false;
                    }
                }
            }
        }

        true
    }
}

impl<T: Eq> Eq for Chunk<T> {}

impl<T> Drop for Chunk<T> {
    fn drop(&mut self) {
        for i in 0..R::ARITY {
            let k = self.kind(i);
            if k == NULL {
                continue;
            }
            unsafe {
                let child = &mut *self.child_ptr(i);
                if k == INNER {
                    ManuallyDrop::drop(&mut child.ptr);
                }
                if k == LEAF {
                    ManuallyDrop::drop(&mut child.leaf);
                }
            }
        }
    }
}

impl<T: Clone + Hash> Clone for Chunk<T> {
    fn clone(&self) -> Chunk<T> {
        let mut res = Chunk {
            bs: self.bs,
            hash: self.hash,
            children: MaybeUninit::uninit(),
        };

        for i in 0..R::ARITY {
            let kind = self.kind(i);
            if kind == NULL {
                continue;
            }
            unsafe {
                if kind == INNER {
                    res.write_chunk(i, self.get_inner(i).clone());
                }
                if kind == LEAF {
                    res.write_leaf(i, self.get_leaf(i).clone());
                }
            }
        }
        res
    }
}

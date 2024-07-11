//! Utilities for pooling object allocations.

use std::{
    cell::RefCell,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr,
    rc::Rc,
};

use fixedbitset::FixedBitSet;

use crate::{
    action::Instr,
    common::{HashMap, HashSet, IndexMap, IndexSet, Value},
    free_join::execute::FrameUpdate,
    hash_index::{BufferedSubset, KeyPresenceTable, SubsetTable},
    offsets::SortedOffsetVector,
    table_spec::Constraint,
    RowId,
};

#[cfg(test)]
mod tests;

/// A trait for types whose allocations can be reused.
pub trait Clear: Default {
    /// Clear the object.
    ///
    /// The end result must be equivalent to `Self::default()`.
    fn clear(&mut self);
    /// Indicate whether or not this object should be reused.
    fn reuse(&self) -> bool {
        true
    }
}

impl<T> Clear for Vec<T> {
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<T: Clear> Clear for Rc<T> {
    fn clear(&mut self) {
        Rc::get_mut(self).unwrap().clear()
    }
    fn reuse(&self) -> bool {
        Rc::strong_count(self) == 1 && Rc::weak_count(self) == 0
    }
}

impl<T: Clear> Clone for Pooled<Rc<T>> {
    fn clone(&self) -> Self {
        Pooled {
            data: self.data.clone(),
            pool: self.pool.clone(),
        }
    }
}

impl<T> Clear for HashSet<T> {
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<K, V> Clear for HashMap<K, V> {
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<K, V> Clear for IndexMap<K, V> {
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<T> Clear for IndexSet<T> {
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl Clear for FixedBitSet {
    fn clear(&mut self) {
        self.clear();
    }
    fn reuse(&self) -> bool {
        !self.is_empty()
    }
}

/// A shared pool of objects.
pub struct Pool<T> {
    data: Rc<RefCell<Vec<T>>>,
}

impl<T> Clone for Pool<T> {
    fn clone(&self) -> Self {
        Pool {
            data: self.data.clone(),
        }
    }
}

impl<T: Clear> Default for Pool<T> {
    fn default() -> Self {
        Pool {
            data: Default::default(),
        }
    }
}

impl<T: Clear> Pool<T> {
    /// Get an empty value of type `T`, potentially reused from the pool.
    pub(crate) fn get(&self) -> Pooled<T> {
        let empty = self.data.borrow_mut().pop().unwrap_or_default();

        Pooled {
            data: ManuallyDrop::new(empty),
            pool: self.clone(),
        }
    }
}

/// An owned value of type `T` that can be returned to a memory pool when it is
/// no longer used.
pub struct Pooled<T: Clear> {
    data: ManuallyDrop<T>,
    pool: Pool<T>,
}

impl<T: Clear + fmt::Debug> fmt::Debug for Pooled<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let data: &T = &self.data;
        data.fmt(f)
    }
}
impl<T: Clear + PartialEq> PartialEq for Pooled<T> {
    fn eq(&self, other: &Self) -> bool {
        // This form rid of a spuriou clippy warning about unconditional recursion.
        <T as PartialEq>::eq(&self.data, &other.data)
    }
}

impl<T: Clear + Eq> Eq for Pooled<T> {}

impl<T: Clear + Hash> Hash for Pooled<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.hash(state)
    }
}

impl<T: Clear> Pooled<T> {
    /// Clear the contents the wrapped object. If the object cannot be reused,
    /// attempt to fetch another value from the pool.
    ///
    /// This method can be used in concert with `relinquish` to provide a
    /// `clear` operation that hands data back to the pool, and then grabs it
    /// back again if it needs to be reused.
    ///
    /// This pattern is likely only suitable for "temporary" buffers.
    pub(crate) fn refresh(this: &mut Pooled<T>) {
        this.data.clear();
        if this.data.reuse() {
            return;
        }
        if let Some(mut other) = this.pool.data.borrow_mut().pop() {
            let slot: &mut T = &mut this.data;
            mem::swap(slot, &mut other);
        }
    }

    /// Transfer the given object to a pool of boxed (`Rc`) objects of the same
    /// type.
    pub(crate) fn transfer_rc(mut this: Pooled<T>, rc_pool: &Pool<Rc<T>>) -> Pooled<Rc<T>> {
        let item: &mut T = &mut this;
        let mut new_container = rc_pool.get();
        let mut_slot = Rc::get_mut(&mut new_container).unwrap();
        mem::swap(mut_slot, item);
        new_container
    }
}

impl<T: Clear + Clone> Pooled<T> {
    pub(crate) fn cloned(this: &Pooled<T>) -> Pooled<T> {
        let mut res = this.pool.get();
        res.clone_from(this);
        res
    }
}

impl<T: Clear> Drop for Pooled<T> {
    fn drop(&mut self) {
        let reuse = self.data.reuse();
        if !reuse {
            // SAFETY: we own `self.data` and being in the drop method means no
            // one else will access it.
            unsafe { ManuallyDrop::drop(&mut self.data) };
            return;
        }
        self.data.clear();
        let t: &T = &self.data;
        // SAFETY: ownership of `self.data` is transferred to the pool
        self.pool.data.borrow_mut().push(unsafe { ptr::read(t) });
    }
}

impl<T: Clear> Deref for Pooled<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T: Clear> DerefMut for Pooled<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

/// Helper trait for allowing the trait resolution system to infer the correct
/// pool type during allocation.
pub trait InPoolSet<PoolSet>
where
    Self: Sized + Clear,
{
    fn get(pool_set: &PoolSet) -> &Pool<Self>;
}

macro_rules! pool_set {
    ($vis:vis $name:ident { $($ident:ident : $ty:ty,)* }) => {
        #[derive(Default)]
        $vis struct $name {
            $(
                $ident: Pool<$ty>,
            )*
        }

        impl $name {
            $vis fn get_pool<T: InPoolSet<Self>>(&self) -> &Pool<T> {
                T::get(self)
            }

            $vis fn get<T: InPoolSet<Self> + Default>(&self) -> Pooled<T> {
                self.get_pool().get()
            }
        }

        $(
            impl InPoolSet<$name> for $ty {
                fn get(pool_set: &$name) -> &Pool<Self> {
                    &pool_set.$ident
                }
            }
        )*
    }
}

pool_set! {
    pub PoolSet {
        vec_vals: Vec<Value>,
        // TODO: work on scaffolding/DI/etc. so that we can share allocations
        // between vec_vals and shared_vals.
        shared_vals: Rc<Vec<Value>>,
        rows: Vec<RowId>,
        offset_vec: SortedOffsetVector,
        column_index: IndexMap<Value, BufferedSubset>,
        constraints: Vec<Constraint>,
        bitsets: FixedBitSet,
        instrs: Vec<Instr>,
        index_hashes: SubsetTable,
        key_presence: KeyPresenceTable,
        frame_updates: FrameUpdate,
        frame_update_vecs: Vec<Pooled<FrameUpdate>>,
    }
}

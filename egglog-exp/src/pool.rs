//! Utilities for allocating and manipulating pools of objects.

use std::{
    cell::RefCell,
    cmp::Ordering,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    ptr,
    rc::Rc,
};

use bumpalo::Bump;
use smallvec::SmallVec;

use crate::{
    common::{DenseIdMap, HashSet, IndexMap, IndexSet},
    free_join::{
        execute::{FrameUpdate, UpdateBatch},
        offset_frame::Slot,
        AtomId, Variable,
    },
    function::{
        index::{ConstantIndex, Index},
        index_cache::IndexCacheResult,
        offsets::{Offset, SortedOffsetSlice, SortedOffsetVector},
        table::TableEntry,
        Value,
    },
};

/// A trait for types whose allocations can be reused.
pub(crate) trait Clear {
    /// Data required to create an empty object.
    type Factory;
    /// Data required to initialize a new object.
    type Args<'a>;
    /// Allocate a new object based on the factory.
    fn new(f: &Self::Factory) -> Self;
    /// Initialize the object using the given arguments.
    fn construct(&mut self, _: &Self::Args<'_>) {}
    /// Clear the object.
    fn clear(&mut self);
    /// Indicate whether or not this object should be reused.
    fn reuse(&self) -> bool {
        true
    }
}

impl<T> Clear for Vec<T> {
    type Factory = ();
    type Args<'a> = ();
    fn new(_: &()) -> Self {
        Vec::default()
    }
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<T> Clear for HashSet<T> {
    type Factory = ();
    type Args<'a> = ();
    fn new(_: &()) -> Self {
        HashSet::default()
    }
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<K, V> Clear for IndexMap<K, V> {
    type Factory = ();
    type Args<'a> = ();
    fn new(_: &()) -> Self {
        Self::default()
    }
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

impl<T> Clear for IndexSet<T> {
    type Factory = ();
    type Args<'a> = ();
    fn new(_: &()) -> Self {
        Self::default()
    }
    fn clear(&mut self) {
        self.clear()
    }
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }
}

/// A pool of clearable objects.
pub(crate) struct Pool<T: Clear> {
    data: RefCell<Vec<T>>,
    factory: T::Factory,
}

impl<T: Clear> Default for Pool<T>
where
    T::Factory: Default,
{
    fn default() -> Pool<T> {
        Self {
            data: RefCell::new(Vec::new()),
            factory: Default::default(),
        }
    }
}

impl<T: Clear> Pool<T> {
    /// Initialize a new Pool.
    pub(crate) fn new(factory: T::Factory) -> Pool<T> {
        Self {
            data: RefCell::new(Vec::new()),
            factory,
        }
    }

    pub(crate) fn deallocate(&self) {
        let mut data = self.data.borrow_mut();
        data.clear();
        data.shrink_to_fit();
    }

    /// Get an empty/cleared object from the pool.
    pub(crate) fn get_default(&self) -> PoolRef<T>
    where
        for<'a> T::Args<'a>: Default,
    {
        self.get(&Default::default())
    }

    /// Get a new object from the pool constructed with the given arguments.
    pub(crate) fn get<'a>(&'a self, args: &T::Args<'_>) -> PoolRef<'a, T> {
        let mut elts = self.data.borrow_mut();
        let mut data = ManuallyDrop::new(elts.pop().unwrap_or_else(|| T::new(&self.factory)));
        data.construct(args);

        PoolRef { data, pool: self }
    }
}

// NB: we could probably build a custom implementation of this type and avoid
// heap allocations for it.
pub(crate) type SharedPoolRef<'a, T> = Rc<PoolRef<'a, T>>;

pub(crate) struct PoolRef<'a, T: Clear> {
    data: ManuallyDrop<T>,
    pool: &'a Pool<T>,
}

impl<'a, T: Clear> PoolRef<'a, T> {
    /// Get the underlying pool reference.
    pub(crate) fn pool(&self) -> &'a Pool<T> {
        self.pool
    }

    /// Convert the reference into a shared reference.
    pub(crate) fn into_shared(self) -> SharedPoolRef<'a, T> {
        Rc::new(self)
    }
}

impl<'a, T: Clear> Drop for PoolRef<'a, T> {
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

impl<'a, T: Clear> Deref for PoolRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.data
    }
}

impl<'a, T: Clear> DerefMut for PoolRef<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

impl<'a, T: Clear + Clone> Clone for PoolRef<'a, T> {
    fn clone(&self) -> PoolRef<'a, T> {
        PoolRef {
            data: self.data.clone(),
            pool: self.pool,
        }
    }
}

impl<'a, T: Clear + Debug> Debug for PoolRef<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data.fmt(f)
    }
}

impl<'a, T: Clear + PartialEq> PartialEq for PoolRef<'a, T> {
    fn eq(&self, other: &PoolRef<'a, T>) -> bool {
        self.data == other.data
    }
}

impl<'a, T: Clear + Eq> Eq for PoolRef<'a, T> {}

impl<'a, T: Clear + Hash> Hash for PoolRef<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.hash(state)
    }
}

impl<'a, T: Clear + PartialOrd> PartialOrd for PoolRef<'a, T> {
    fn partial_cmp(&self, other: &PoolRef<'a, T>) -> Option<Ordering> {
        self.data.partial_cmp(&other.data)
    }
}

impl<'a, T: Clear + Ord> Ord for PoolRef<'a, T> {
    fn cmp(&self, other: &PoolRef<'a, T>) -> Ordering {
        self.data.cmp(&other.data)
    }
}

/// We have a lot of pools. PoolSet is a group of pools whose lifetimes are all
/// determined by a single arena. This allows us to centralize the plumbing of
/// pools together when one pool has to reference another, and use the type
/// system to simplify allocation from individual pools.
pub struct PoolSet<'a> {
    offsets: &'a Pool<SortedOffsetVector>,
    indexes: &'a Pool<Index<'a>>,
    constant_indexes: &'a Pool<ConstantIndex<'a>>,
    replacements: &'a Pool<Vec<(usize, Slot<'a, *const SortedOffsetSlice>)>>,
    frame_updates: &'a Pool<FrameUpdate<'a>>,
    update_batches: &'a Pool<UpdateBatch<'a>>,
    index_context: &'a Pool<Vec<(AtomId, IndexCacheResult<'a, Index<'a>>, usize)>>,
    seen_combinations: &'a Pool<HashSet<SmallVec<[Value; 4]>>>,
    bindings: &'a Pool<DenseIdMap<Variable, Value>>,
    rebuild_index: &'a Pool<IndexSet<Offset>>,
    rebuild_work: &'a Pool<Vec<(TableEntry, TableEntry)>>,
    vals: &'a Pool<Vec<Value>>,
}

impl<'a> PoolSet<'a> {
    pub fn new(arena: &'a Bump) -> PoolSet<'a> {
        let offsets: &Pool<_> = arena.alloc(Pool::default());
        let indexes = arena.alloc(Pool::new(offsets));
        let constant_indexes = arena.alloc(Pool::new(offsets));
        let index_context = arena.alloc(Pool::default());
        let replacements = arena.alloc(Pool::default());
        let frame_updates = arena.alloc(Pool::default());
        let update_batches = arena.alloc(Pool::default());
        let seen_combinations = arena.alloc(Pool::default());
        let bindings = arena.alloc(Pool::default());
        let rebuild_index = arena.alloc(Pool::default());
        let rebuild_work = arena.alloc(Pool::default());
        let vals = arena.alloc(Pool::default());
        PoolSet {
            offsets,
            indexes,
            constant_indexes,
            index_context,
            replacements,
            frame_updates,
            update_batches,
            seen_combinations,
            bindings,
            rebuild_index,
            rebuild_work,
            vals,
        }
    }
    pub(crate) fn get<T: InPoolSet<'a>>(&self) -> &'a Pool<T> {
        T::get(self)
    }
    pub(crate) fn get_default<T: InPoolSet<'a>>(&self) -> PoolRef<'a, T>
    where
        for<'b> T::Args<'b>: Default,
    {
        self.get::<T>().get_default()
    }
}

impl<'a> Drop for PoolSet<'a> {
    fn drop(&mut self) {
        // These pools will not get dropped on their own. Deallocate the
        // underlying memory.
        //
        // None of this is unsafe, but if we change the layout of Pool at some
        // point we could leak memory if we aren't careful to change the
        // implementation of 'deallocate'.
        self.offsets.deallocate();
        self.indexes.deallocate();
        self.constant_indexes.deallocate();
        self.index_context.deallocate();
        self.replacements.deallocate();
        self.frame_updates.deallocate();
        self.update_batches.deallocate();
        self.seen_combinations.deallocate();
        self.bindings.deallocate();
        self.rebuild_index.deallocate();
        self.rebuild_work.deallocate();
    }
}

pub(crate) trait InPoolSet<'a>: Clear + Sized {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self>;
}

impl<'a> InPoolSet<'a> for Index<'a> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.indexes
    }
}

impl<'a> InPoolSet<'a> for ConstantIndex<'a> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.constant_indexes
    }
}

impl<'a> InPoolSet<'a> for SortedOffsetVector {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.offsets
    }
}

impl<'a> InPoolSet<'a> for Vec<(usize, Slot<'a, *const SortedOffsetSlice>)> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.replacements
    }
}

impl<'a> InPoolSet<'a> for FrameUpdate<'a> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.frame_updates
    }
}

impl<'a> InPoolSet<'a> for UpdateBatch<'a> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.update_batches
    }
}

impl<'a> InPoolSet<'a> for Vec<(AtomId, IndexCacheResult<'a, Index<'a>>, usize)> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.index_context
    }
}

impl<'a> InPoolSet<'a> for HashSet<SmallVec<[Value; 4]>> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.seen_combinations
    }
}

impl<'a> InPoolSet<'a> for DenseIdMap<Variable, Value> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.bindings
    }
}

impl<'a> InPoolSet<'a> for IndexSet<Offset> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.rebuild_index
    }
}

impl<'a> InPoolSet<'a> for Vec<(TableEntry, TableEntry)> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.rebuild_work
    }
}

impl<'a> InPoolSet<'a> for Vec<Value> {
    fn get(pools: &PoolSet<'a>) -> &'a Pool<Self> {
        pools.vals
    }
}

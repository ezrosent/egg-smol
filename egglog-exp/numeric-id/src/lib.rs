//! A crate with utilities for working with numeric Ids.
use std::{
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
    ops,
};

#[cfg(test)]
mod tests;

/// A trait describing "newtypes" that wrap an integer.
pub trait NumericId: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    fn from_usize(index: usize) -> Self;
    fn index(self) -> usize;
    fn inc(self) -> Self {
        Self::from_usize(self.index() + 1)
    }
}

impl NumericId for usize {
    fn from_usize(index: usize) -> Self {
        index
    }

    fn index(self) -> usize {
        self
    }
}

/// A mapping from a [`NumericId`] to some value.
///
/// This mapping is _dense_: it stores a flat array indexed by `K::index()`,
/// with no hashing. For sparse mappings, use a HashMap.
#[derive(Clone)]
pub struct DenseIdMap<K, V> {
    data: Vec<Option<V>>,
    _marker: PhantomData<K>,
}

impl<K: NumericId + Debug, V: Debug> Debug for DenseIdMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (k, v) in self.iter() {
            map.entry(&k, v);
        }
        map.finish()
    }
}

impl<K, V> Default for DenseIdMap<K, V> {
    fn default() -> Self {
        Self {
            data: Vec::new(),
            _marker: PhantomData,
        }
    }
}

impl<K: NumericId, V> DenseIdMap<K, V> {
    /// Create an empty map with space for `n` entries pre-allocated.
    pub fn with_capacity(n: usize) -> Self {
        let mut res = Self::new();
        res.reserve_space(K::from_usize(n));
        res
    }

    /// Create an empty map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Clear the table's contents.
    pub fn clear(&mut self) {
        self.data.clear();
    }

    /// Get the current capacity for the table.
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Get the number of ids currently indexed by the table (including "null"
    /// entries). This is a less useful version of "length" in other containers.
    pub fn n_ids(&self) -> usize {
        self.data.len()
    }

    /// Insert the given mapping into the table.
    pub fn insert(&mut self, key: K, value: V) {
        self.reserve_space(key);
        self.data[key.index()] = Some(value);
    }

    /// Get the key that would be returned by the next call to [`DenseIdMap::push`].
    pub fn next_id(&self) -> K {
        K::from_usize(self.data.len())
    }

    /// Add the given mapping to the table, returning the key corresponding to
    /// [`DenseIdMap::n_ids`].
    pub fn push(&mut self, val: V) -> K {
        let res = self.next_id();
        self.data.push(Some(val));
        res
    }

    /// Get the current mapping for `key` in the table.
    pub fn get(&self, key: K) -> Option<&V> {
        self.data.get(key.index())?.as_ref()
    }

    /// Get a mutable reference to the current mapping for `key` in the table.
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.reserve_space(key);
        self.data.get_mut(key.index())?.as_mut()
    }

    /// Extract the value mapped to by `key` from the table.
    ///
    /// # Panics
    /// This method panics if `key` is not in the table.
    pub fn take(&mut self, key: K) -> V {
        self.reserve_space(key);
        self.data.get_mut(key.index()).unwrap().take().unwrap()
    }

    /// Get the current mapping for `key` in the table, or insert the value
    /// returned by `f` and return a mutable reference to it.
    pub fn get_or_insert(&mut self, key: K, f: impl FnOnce() -> V) -> &mut V {
        self.reserve_space(key);
        self.data[key.index()].get_or_insert_with(f)
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.data
            .iter()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_ref()?)))
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_mut()?)))
    }

    /// Reserve space up to the given key in the table.
    pub fn reserve_space(&mut self, key: K) {
        let index = key.index();
        if index >= self.data.len() {
            self.data.resize_with(index + 1, || None);
        }
    }
}

impl<K: NumericId, V> ops::Index<K> for DenseIdMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: NumericId, V> ops::IndexMut<K> for DenseIdMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

impl<K: NumericId, V: Default> DenseIdMap<K, V> {
    pub fn get_or_default(&mut self, key: K) -> &mut V {
        self.get_or_insert(key, V::default)
    }
}

#[cfg(not(feature = "debug-val-trace"))]
mod context {
    #[derive(Copy, Clone, Debug)]
    pub struct ContextHandle;

    impl ContextHandle {
        #[inline(always)]
        pub fn new(_: impl Into<String>) -> ContextHandle {
            ContextHandle::empty()
        }

        pub const fn empty() -> ContextHandle {
            ContextHandle
        }
    }
}

#[cfg(feature = "debug-val-trace")]
mod context {
    use std::{backtrace::Backtrace, fmt, sync::Mutex};

    use lazy_static::lazy_static;
    use std::collections::HashMap;

    #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ContextHandle(usize);

    impl ContextHandle {
        pub fn new(message: impl Into<String>) -> ContextHandle {
            let mut map = CONTEXT_MAP.contents.lock().unwrap();
            let handle = ContextHandle(map.len());
            map.insert(handle, Context::new(message));
            handle
        }
        pub const fn empty() -> ContextHandle {
            ContextHandle(!0)
        }
    }

    impl fmt::Debug for ContextHandle {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let map = CONTEXT_MAP.contents.lock().unwrap();
            write!(f, "{:?}", map.get(self).unwrap())
        }
    }

    pub(crate) struct Context {
        pub(crate) backtrace: Backtrace,
        pub(crate) extra: String,
    }

    impl Context {
        pub(crate) fn new(message: impl Into<String>) -> Context {
            Context {
                extra: message.into(),
                backtrace: Backtrace::force_capture(),
            }
        }
    }

    impl fmt::Debug for Context {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.extra.is_empty() {
                write!(f, "{}", self.backtrace)
            } else {
                write!(f, "{}:\n{}", self.extra, self.backtrace)
            }
        }
    }

    #[derive(Default)]
    pub(crate) struct ContextMap {
        contents: Mutex<HashMap<ContextHandle, Context>>,
    }

    lazy_static! {
        pub(crate) static ref CONTEXT_MAP: ContextMap = ContextMap::default();
    }
}

pub use context::ContextHandle;

#[macro_export]
macro_rules! define_id {
    ($v:vis $name:ident, $repr:ty) => { define_id!($v, $name, $repr, ""); };
    ($v:vis $name:ident, $repr:ty, $doc:tt) => {
        #[derive(Copy, Clone)]
        #[doc = $doc]
        $v struct $name {
            rep: $repr,
            #[allow(unused)]
            context: $crate::ContextHandle,
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.rep == other.rep
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.rep.cmp(&other.rep)
            }
        }

        impl std::hash::Hash for $name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                self.rep.hash(state);
            }
        }

        impl $name {
            $v fn with_context(id: $repr, message: impl Into<String>) -> Self {
                $name {
                    rep: id,
                    context: $crate::ContextHandle::new(message)
                }
            }

            $v fn new(id: $repr) -> Self {
                Self::with_context(id, "")
            }

            #[allow(unused)]
            $v const fn new_const(id: $repr) -> Self {
                $name {
                    rep: id,
                    context: $crate::ContextHandle::empty(),
                }
            }

            #[allow(unused)]
            $v fn range(low: Self, high: Self) -> impl Iterator<Item = Self> {
                (low.rep..high.rep).map(|i| $name::new(i))
            }

            #[allow(unused)]
            $v fn rep(self) -> $repr {
                self.rep
            }
        }

        impl $crate::NumericId for $name {
            fn from_usize(index: usize) -> Self {
                assert!(<$repr>::MAX as usize >= index,
                    "overflowing id type {} (represented as {}) with index {}", stringify!($name), stringify!($repr), index);
                $name::new(index as $repr)
            }
            fn index(self) -> usize {
                self.rep as usize
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
                #[cfg(not(feature = "debug-val-trace"))]
                {
                    write!(fmt, "{}({:?})", stringify!($name), self.rep)
                }
                #[cfg(feature = "debug-val-trace")]
                {
                    write!(fmt, "{}({:?}){{\n{:?}\n}}", stringify!($name), self.rep, self.context)
                }
            }
        }
    };
}

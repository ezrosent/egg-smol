use std::{
    fmt::{self, Debug},
    hash::{BuildHasherDefault, Hash, Hasher},
    marker::PhantomData,
    ops,
};

use hashbrown::raw::RawTable;
use rustc_hash::FxHasher;

use crate::pool::Clear;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type HashSet<T> = hashbrown::HashSet<T, BuildHasherDefault<FxHasher>>;
pub(crate) type IndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<FxHasher>>;
pub(crate) type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasherDefault<FxHasher>>;

pub trait NumericId: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    fn from_usize(index: usize) -> Self;
    fn index(self) -> usize;
}

impl NumericId for usize {
    fn from_usize(index: usize) -> Self {
        index
    }

    fn index(self) -> usize {
        self
    }
}

/// An intern table mapping a key to some numeric id type.
///
/// This is primarily used to manage the [`Value`]s associated with a a
/// primtiive value.
pub struct InternTable<K, V> {
    vals: Vec<K>,
    data: RawTable<V>,
}

impl<K, V> Default for InternTable<K, V> {
    fn default() -> Self {
        Self {
            vals: Default::default(),
            data: Default::default(),
        }
    }
}

impl<K: Eq + Hash + Clone, V: NumericId> InternTable<K, V> {
    pub fn intern(&mut self, k: &K) -> V {
        let hash = hash_value(k);
        if let Some(v) = self.data.get(hash, |v| k == &self.vals[v.index()]) {
            *v
        } else {
            let res = V::from_usize(self.vals.len());
            self.vals.push(k.clone());
            *self
                .data
                .insert_entry(hash, res, |v| hash_value(&self.vals[v.index()]))
        }
    }

    pub fn get(&self, v: V) -> &K {
        &self.vals[v.index()]
    }
}

fn hash_value(v: &impl Hash) -> u64 {
    let mut hasher = FxHasher::default();
    v.hash(&mut hasher);
    hasher.finish()
}

/// A mapping from a [`NumericId`] to some value.
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

impl<K, V> Clear for DenseIdMap<K, V> {
    type Args<'a> = ();
    type Factory = ();

    fn new(_: &()) -> Self {
        Self::default()
    }

    fn reuse(&self) -> bool {
        self.data.reuse()
    }

    fn clear(&mut self) {
        self.data.clear();
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

impl<K: NumericId, V: Clone> DenseIdMap<K, V> {
    /// Clear any contents in the current map and replace it with a copy of the
    /// contents of `other`.
    pub(crate) fn copy_from(&mut self, other: &DenseIdMap<K, V>) {
        self.data.clear();
        self.data.extend_from_slice(&other.data);
    }
}

impl<K: NumericId, V> DenseIdMap<K, V> {
    pub(crate) fn with_capacity(n: usize) -> Self {
        let mut res = Self::new();
        res.reserve_space(K::from_usize(n));
        res
    }
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn n_ids(&self) -> usize {
        self.data.len()
    }

    pub(crate) fn insert(&mut self, key: K, value: V) {
        self.reserve_space(key);
        self.data[key.index()] = Some(value);
    }

    pub(crate) fn push(&mut self, val: V) -> K {
        let res = K::from_usize(self.data.len());
        self.data.push(Some(val));
        res
    }

    pub(crate) fn get(&self, key: K) -> Option<&V> {
        self.data.get(key.index())?.as_ref()
    }

    pub(crate) fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.reserve_space(key);
        self.data.get_mut(key.index())?.as_mut()
    }

    pub(crate) fn take(&mut self, key: K) -> V {
        self.reserve_space(key);
        self.data.get_mut(key.index()).unwrap().take().unwrap()
    }

    pub(crate) fn get_or_insert(&mut self, key: K, f: impl FnOnce() -> V) -> &mut V {
        self.reserve_space(key);
        self.data[key.index()].get_or_insert_with(f)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.data
            .iter()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_ref()?)))
    }
    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .filter_map(|(i, v)| Some((K::from_usize(i), v.as_mut()?)))
    }

    pub(crate) fn reserve_space(&mut self, key: K) {
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
    #[cfg(test)]
    pub(crate) fn get_or_default(&mut self, key: K) -> &mut V {
        self.get_or_insert(key, V::default)
    }
}

#[cfg(not(feature = "debug-val-trace"))]
mod context {
    #[derive(Copy, Clone, Debug)]
    pub(crate) struct ContextHandle;

    impl ContextHandle {
        #[inline(always)]
        pub(crate) fn new(_: impl Into<String>) -> ContextHandle {
            ContextHandle
        }
    }
}

#[cfg(feature = "debug-val-trace")]
mod context {
    use std::{backtrace::Backtrace, fmt, sync::Mutex};

    use hashbrown::HashMap;
    use lazy_static::lazy_static;

    #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    pub(crate) struct ContextHandle(usize);

    impl ContextHandle {
        pub(crate) fn new(message: impl Into<String>) -> ContextHandle {
            let mut map = CONTEXT_MAP.contents.lock().unwrap();
            let handle = ContextHandle(map.len());
            map.insert(handle, Context::new(message));
            handle
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

pub(crate) use context::ContextHandle;

#[macro_export]
macro_rules! define_id {
    (pub $name:ident, $repr:ty) => { define_id!([pub], $name, $repr, ""); };
    (pub $name:ident, $repr:ty, $doc:tt) => { define_id!([pub], $name, $repr, $doc); };
    (pub(crate) $name:ident, $repr:ty) => { define_id!([pub(crate)], $name, $repr, ""); };
    (pub(crate) $name:ident, $repr:ty, $doc:tt) => { define_id!([pub(crate)], $name, $repr, $doc); };
    ($name:ident, $repr:ty) => { define_id!([], $name, $repr, ""); };
    ($name:ident, $repr:ty, $doc:tt) => { define_id!([], $name, $repr, $doc); };
    ([$($prefix:tt)*], $name:ident, $repr:ty, $doc:tt) => {
        #[derive(Copy, Clone)]
        #[doc = $doc]
        $($prefix)* struct $name {
            rep: $repr,
            #[allow(unused)]
            context: $crate::common::ContextHandle,
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.rep == other.rep
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.rep.partial_cmp(&other.rep)
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
            $($prefix)* fn with_context(id: $repr, message: impl Into<String>) -> Self {
                $name {
                    rep: id,
                    context: $crate::common::ContextHandle::new(message)
                }
            }

            $($prefix)* fn new(id: $repr) -> Self {
                Self::with_context(id, "")
            }

            #[allow(unused)]
            $($prefix)* fn range(low: Self, high: Self) -> impl Iterator<Item = Self> {
                (low.rep..high.rep).map(|i| $name::new(i))
            }
        }

        impl $crate::common::NumericId for $name {
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

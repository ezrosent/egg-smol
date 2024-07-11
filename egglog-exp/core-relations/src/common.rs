use std::hash::{BuildHasherDefault, Hash, Hasher};

use hashbrown::raw::RawTable;
use numeric_id::{define_id, DenseIdMap, NumericId};
use rustc_hash::FxHasher;

use crate::pool::Clear;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type HashSet<T> = hashbrown::HashSet<T, BuildHasherDefault<FxHasher>>;
pub(crate) type IndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<FxHasher>>;
pub(crate) type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasherDefault<FxHasher>>;

/// An intern table mapping a key to some numeric id type.
///
/// This is primarily used to manage the [`Value`]s associated with a a
/// primtiive value.
#[derive(Clone)]
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

impl<K: NumericId, V> Clear for DenseIdMap<K, V> {
    fn reuse(&self) -> bool {
        self.capacity() > 0
    }

    fn clear(&mut self) {
        self.clear();
    }
}

define_id!(pub Value, u32, "A generic identifier representing an egglog value");

impl Value {
    pub(crate) fn stale() -> Self {
        Value::new(u32::MAX)
    }
    /// Values have a special "Stale" value that is used to indicate that the
    /// value isn't intended to be read.
    pub(crate) fn set_stale(&mut self) {
        self.rep = u32::MAX;
    }

    /// Whether or not the given value is stale. See [`Value::set_stale`].
    pub(crate) fn is_stale(&self) -> bool {
        self.rep == u32::MAX
    }
}

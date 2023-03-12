//! A simple implementation of ZDDs with an eye toward efficient egraph
//! extraction.

pub(crate) mod egraph;
pub(crate) mod fixed_cache;
pub(crate) mod greedy_extract;
pub(crate) mod zdd;

#[cfg(test)]
mod tests;

pub use egraph::{choose_nodes, Dag, Egraph};
pub use greedy_extract::extract_greedy;
pub use zdd::{Report, Zdd, ZddPool};

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;
type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
type HashSet<T> = hashbrown::HashSet<T, BuildHasherDefault<FxHasher>>;

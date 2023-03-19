//! A simple implementation of ZDDs with an eye toward efficient egraph
//! extraction.

pub(crate) mod egraph;
pub(crate) mod extract;
pub(crate) mod fixed_cache;
pub(crate) mod zdd;

#[cfg(test)]
mod tests;

pub use egraph::{choose_nodes, render_zdd, Egraph};
pub use extract::{extract_greedy, extract_zdd, Dag, ExtractResult};
pub use zdd::{gc_zdds, Report, Zdd, ZddPool};

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;
type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
type HashSet<T> = hashbrown::HashSet<T, BuildHasherDefault<FxHasher>>;

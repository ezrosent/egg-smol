//! A simple implementation of ZDDs with an eye toward efficient egraph
//! extraction.

pub(crate) mod egraph;
pub(crate) mod fixed_cache;
pub(crate) mod zdd;

#[cfg(test)]
mod tests;

pub use egraph::{choose_nodes, Egraph};
pub use zdd::{Report, Zdd, ZddPool};

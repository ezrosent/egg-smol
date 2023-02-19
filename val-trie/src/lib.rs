//! A persistent set data-structure optimized for efficient hasing and storing
//! integer keys.

pub(crate) mod node;
pub(crate) mod set;

pub use set::IntSet;

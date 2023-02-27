//! A persistent set data-structure optimized for efficient hasing and storing
//! integer keys. This data-structure is an immutable radix tree / trie:
//!
//! * The node representation is inspired by the one used in the `im` crate's
//! HAMT implementation. We currently store 5 bits per level, but the core
//! implementation is designed to support multiple node widths.
//!
//! * Like the ART, we compress shared prefixes and store leaves inline if they
//! are the only node present in a given subtree. We store bitwise prefixes
//! (rounded down to the bit-width of the level), and leverage the fact that
//! keys are always 64 bits to store the prefix as an integer. This simplifies a
//! number of prefix computations and other details form the ART design.
//!
//! * As in both the ART and HAMT, a set has a single canonical representation
//! which makes structural comparison simpler.
//!
//! * We store subtree hashes in interior nodes and leverage the hashes along
//! with pointer equality to speed up comparisons. This feature makes it
//! efficient to store a set or map as a _key_ in a hashmap.
//!
//! These features are optimized for use in egglog. We want to make maps and
//! sets first-class egglog values. Egglog doesn't support arbitrary mutation,
//! so a persistent data-structure is key, but this trie goes beyond that:
//!
//! * egglog values are usually pre-interned as integers: we can build a trie
//! that takes this into account and avoids the overhead of a sparse key space
//! when storing the data in a trie.
//!
//! * `Id`s are generated by a counter, so any given set of ids is going to be
//! dense: ART-style prefix compression will shrink the resulting trie,
//! resulting in faster lookups and less space overhead when compared with a
//! standard HAMT.
//!
//! * egglog values are frequently stored inside of a hash-map of some sort:
//! efficient hashing and equality comparisons are therefore extremely
//! important.
//!
//! The core `node` module is structured in a way that would make a general
//! Hash Table possible to implement.

pub(crate) mod hash_node;
pub(crate) mod map;
pub(crate) mod node;
pub(crate) mod set;
#[cfg(test)]
pub(crate) mod test_workloads;

pub use map::IntMap;
pub use set::hash_set::HashSet;
pub use set::IntSet;

// pub use node::new_node::IntSet as NewIntSet;

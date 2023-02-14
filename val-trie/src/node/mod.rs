//! Interior nodes for the trie.

use std::{mem, rc::Rc};

#[cfg(test)]
mod tests;

// TODO:
// * support 64-bit keys (ideally giving better performance for 32-bit via
// prefix compression)
// * wider arity, but make it parametric so we can test different values.
//
// 32 bits - hashcode
// 32 bits - bitset
// 64 bits - prefix
// 64 * popcnt(bitset) -- 256 bytes + 16, 272 bytes per node. pretty big, but
// well within a cache line. We can probably do dense for now, build sparse
// later.
// Idea:
// - "map sort" gives you a Table storing tuples in a fairly "flat" way.
// - Store offsets into Table in the tries.
// - Store pointers back to tries in the table, use that as an index.

#[repr(transparent)]
#[derive(Copy, Clone, Default)]
struct Bitset(u16);

const MAX_CHILDREN: usize = mem::size_of::<Bitset>() * 8;

impl Bitset {
    /// Whether 'bit' is set in the set. The behavior is unspecified if 'bit' is
    /// out of range.
    fn contains(&self, bit: usize) -> bool {
        debug_assert!(bit < MAX_CHILDREN);
        (self.0 & (1u16.wrapping_shl(bit as u32))) != 0
    }

    /// The number of set bits.
    fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    /// The number of bits below 'bit' that are set. The behavior is unspecified
    /// if 'bit' is out of range.
    fn rank(&self, bit: usize) -> usize {
        debug_assert!(bit < MAX_CHILDREN);
        let mask = !((!0u16).wrapping_shl(bit as u32));
        (self.0 & mask).count_ones() as usize
    }

    /// Set 'bit'. The behavior is unspecified if 'bit' is out of range.
    fn set(&mut self, bit: usize) {
        debug_assert!(bit < MAX_CHILDREN);
        self.0 |= 1u16.wrapping_shl(bit as u32);
    }
}

// TODO: implement prefix.
// * Prefix is up to 3.5 bytes in length. Last nibble is used to encode the
// length of the prefix (in nibbles)
#[derive(Copy, Clone)]
struct Prefix(u32);

// * experiment with increasing this to 32 bits. It's nice to have the header be 64 bits exactly though (full inline rep just > 1K)
#[derive(Copy, Clone)]
struct HashCode(u16);

pub(crate) struct Node {
    // TODO: store children inline
    children: Vec<Rc<Node>>,
    prefix: Prefix,
    mask: Bitset,
    hash: HashCode,
}

impl Node {}

// TODO: we will always "know" when our traversal is done based on our progress
// from the root. That means we could pick out leaves without any tagging.
// Alternative, less rust-hostile: leaves are stored inline whenever the header
// indicates a single child. That, or a pointer tagging scheme?

// Alternative would be to

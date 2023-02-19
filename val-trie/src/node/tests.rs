use super::*;

/*
use super::{Bitset, Prefix};

#[test]
fn basic_bitset() {
    let mut bs = Bitset::default();
    bs.set(0);
    bs.set(1);
    bs.set(4);
    bs.set(5);

    assert_eq!(bs.len(), 4);

    assert!(bs.contains(0));
    assert!(bs.contains(1));
    assert!(!bs.contains(2));
    assert!(!bs.contains(3));
    assert!(bs.contains(4));
    assert!(bs.contains(5));

    assert_eq!(bs.rank(0), 0);
    assert_eq!(bs.rank(1), 1);
    assert_eq!(bs.rank(4), 2);
    assert_eq!(bs.rank(5), 3);
}

#[test]
fn basic_prefix() {
    fn check_prefix(k1: u64, k2: u64, mask: u64, len: usize) {
        let (prefix, got_len) = Prefix::new(k1, k2);
        let (got_mask, got_len2) = prefix.unpack();
        assert_eq!(got_mask, mask);
        assert_eq!(len, got_len);
        assert_eq!(len, got_len2);
    }
    check_prefix(1, 3, 1, 1);
    check_prefix(1, 4, 0, 0);
    check_prefix(!0, !0, !(63 << 58), 58);
}
*/

// What to do with the missing bit?
// first: max prefix is 63 bits, otherwise it's the same key.
// Suppose we had two keys that shared 63 bits of their prefix:
// 58 bits of the prefix are accounted for in the Prefix. which means the next 5
// bits are going to be the same. We pay an extra node.
// We could steal bits from the hash code.

// Step 1: get a working data-structure
// * finish header
//   (header, packing, MSB, etc.)
// * finish node (yield a usize for now, then figure out traits for values later)
//
// * finish data-structure
// Step 2: hash-consing

/*
struct Header {
    Prefix: 64
    Prefix Len: 6
    Hash Code: 26
    BitSet: 32,
}

*/

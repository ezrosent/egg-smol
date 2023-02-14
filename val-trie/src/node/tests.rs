use super::Bitset;

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

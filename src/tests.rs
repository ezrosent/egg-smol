use super::*;

#[test]
fn binary_search() {
    let mut map = IndexMap::default();
    assert_eq!(binary_search_by_key(&map, |v| v, &0), None);
    map.insert(1, 1);
    assert_eq!(binary_search_by_key(&map, |v| v, &0), Some(0));
    map.clear();
    for i in 0..128 {
        // have a run of 4 24s and then skip to 26
        let v = if i == 50 || i == 51 { 24 } else { i / 2 };
        map.insert(i, v);
    }

    assert_eq!(binary_search_by_key(&map, |v| v, &3), Some(6));
    assert_eq!(binary_search_by_key(&map, |v| v, &0), Some(0));
    assert_eq!(binary_search_by_key(&map, |v| v, &63), Some(126));
    assert_eq!(binary_search_by_key(&map, |v| v, &200), None);
    assert_eq!(binary_search_by_key(&map, |v| v, &-3), Some(0));
    assert_eq!(binary_search_by_key(&map, |v| v, &24), Some(48));
    assert_eq!(binary_search_by_key(&map, |v| v, &25), Some(52));
}

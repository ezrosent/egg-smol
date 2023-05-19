use bumpalo::Bump;

use crate::{
    common::NumericId,
    free_join::offset_frame::{OffsetFrame, Slot},
    function::offsets::{Offset, RangeOrSlice, SortedOffsetSlice, SortedOffsetVector},
    pool::PoolSet,
};

#[test]
fn frame() {
    let bump = Bump::default();
    let poolset = PoolSet::new(&bump);
    fn offs(x: impl IntoIterator<Item = usize>) -> SortedOffsetVector {
        SortedOffsetVector::new(x.into_iter().map(Offset::from_usize).collect())
    }
    fn lift(x: &SortedOffsetVector) -> RangeOrSlice<&SortedOffsetSlice> {
        RangeOrSlice::Slice(x.slice())
    }

    fn check_eq(x: Option<&Slot<&SortedOffsetSlice>>, y: &SortedOffsetVector) {
        assert_eq!(x.map(Slot::offsets), Some(&lift(y)));
    }

    let o1 = offs(vec![1, 2, 3]);
    let o2 = offs(vec![2, 3, 4]);
    let mut v = vec![Slot::new(lift(&o1)), Slot::new(lift(&o2))];
    let mut f1 = OffsetFrame::new(&mut v, poolset.get());
    check_eq(f1.get(1), &o2);
    unsafe {
        let x = offs(vec![4, 5, 6]);
        let mut f2 = f1.narrow();
        check_eq(f2.get(0), &o1);
        f2.replace(0, lift(&x));
        check_eq(f2.get(0), &x);
        {
            let y = offs(vec![7, 8, 9]);
            let mut f3 = f2.narrow();
            f3.replace(1, lift(&y));
            check_eq(f3.get(0), &x);
            check_eq(f3.get(1), &y);
        }
        check_eq(f2.get(0), &x);
    }
    check_eq(f1.get(0), &o1);
}

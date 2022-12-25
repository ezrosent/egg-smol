use crate::{TupleOutput, Value};

use super::FlatVec;

fn val(i: impl Into<Value>) -> Value {
    i.into()
}

#[test]
fn retain_live() {
    let mut fv = FlatVec::new(2);
    fv.push(0, &[val(0), val(1)], val(16));
    fv.push(1, &[val(2), val(3)], val(17));
    fv.push(1, &[val(4), val(5)], val(18));
    fv.push(2, &[val(6), val(7)], val(18));
    fv.push(2, &[val(8), val(9)], val(18));

    fv.set_stale(1, 3);
    fv.set_stale(4, 3);

    let mut retained: Vec<Vec<Value>> = Vec::new();

    fv.retain_live(|vs| {
        retained.push(vs.into());
    });

    assert_eq!(
        retained,
        vec![
            vec![val(0), val(1)],
            vec![val(4), val(5)],
            vec![val(6), val(7)],
        ]
    );

    let remaining = Vec::from_iter(fv.iter_range(0..100));

    assert_eq!(
        remaining,
        vec![
            (
                0,
                &[val(0), val(1)][..],
                &TupleOutput {
                    value: val(16),
                    timestamp: 0
                }
            ),
            (
                1,
                &[val(4), val(5)],
                &TupleOutput {
                    value: val(18),
                    timestamp: 1
                }
            ),
            (
                2,
                &[val(6), val(7)],
                &TupleOutput {
                    value: val(18),
                    timestamp: 2
                }
            ),
        ]
    );
}

#[test]
fn push_index() {
    let mut fv = FlatVec::new(1);
    fv.push(0, &[val(0)], val(1));
    fv.push(1, &[val(1)], val(2));
    fv.push(1, &[val(2)], val(3));

    let (ins, out) = fv.get(1).unwrap();
    assert_eq!(ins, &[val(1)]);
    assert_eq!(
        out,
        &TupleOutput {
            value: val(2),
            timestamp: 1
        }
    );
    fv.set_stale(0, 3);

    let entries = Vec::from_iter(fv.iter_range(0..100));
    assert_eq!(
        entries,
        vec![
            (
                1,
                &[val(1)][..],
                &TupleOutput {
                    value: val(2),
                    timestamp: 1
                }
            ),
            (
                2,
                &[val(2)],
                &TupleOutput {
                    value: val(3),
                    timestamp: 1
                }
            ),
        ]
    );
}

#[test]
#[should_panic]
fn arity_mismatch() {
    let mut fv = FlatVec::new(2);
    fv.push(0, &[val(0), val(1), val(2)], val(3));
}

use std::io::stderr;

use num_rational::Rational64;

use crate::{add_expressions, define_rule, ColumnTy, DefaultVal, EGraph, MergeFn};

#[test]
fn ac() {
    const N: usize = 5;
    let mut egraph = EGraph::default();
    let int_prim = egraph.primitives_mut().get_ty::<i64>();
    let num_table = egraph.add_table(
        vec![ColumnTy::Primitive(int_prim), ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "num",
    );
    let add_table = egraph.add_table(
        vec![ColumnTy::Id; 3],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "add",
    );

    let add_comm = define_rule! {
        [egraph] ((-> (add_table x y) id))
              => ((set (add_table y x) id))
    };

    let add_assoc = define_rule! {
        [egraph] ((-> (add_table x (add_table y z)) id))
              => ((set (add_table (add_table x y) z) id))
    };

    // Running these rules on an empty database should change nothing.
    assert!(!egraph.run_rules(&[add_comm, add_assoc]).unwrap());

    // Fill the database.
    let mut ids = Vec::new();
    //  Add 0 .. N to the database.
    let num_rows = (0..N)
        .map(|i| {
            let id = egraph.fresh_id();
            let i = egraph.primitives_mut().get(i as i64);
            ids.push(id);
            (num_table, vec![i, id])
        })
        .collect::<Vec<_>>();
    egraph.add_values(num_rows);

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut to_add = Vec::new();
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![*num, prev, id]));
            prev = id;
        }
        let left_root = to_add.last().unwrap().1[2];
        prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter() {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![prev, *num, id]));
            prev = id;
        }
        let right_root = to_add.last().unwrap().1[2];
        egraph.add_values(to_add);
        (left_root, right_root)
    };
    // Saturate
    while egraph.run_rules(&[add_comm, add_assoc]).unwrap() {}
    let canon_left = egraph.get_canon(left_root);
    let canon_right = egraph.get_canon(right_root);
    assert_eq!(canon_left, canon_right);
}

#[test]
fn ac_tracing() {
    const N: usize = 5;
    let mut egraph = EGraph::with_tracing();
    let int_prim = egraph.primitives_mut().get_ty::<i64>();
    let num_table = egraph.add_table(
        vec![ColumnTy::Primitive(int_prim), ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "num",
    );
    let add_table = egraph.add_table(
        vec![ColumnTy::Id; 3],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "add",
    );

    let add_comm = define_rule! {
        [egraph] ((-> (add_table x y) id))
              => ((set (add_table y x) id))
    };

    let add_assoc = define_rule! {
        [egraph] ((-> (add_table x (add_table y z)) id))
              => ((set (add_table (add_table x y) z) id))
    };

    // Running these rules on an empty database should change nothing.
    assert!(!egraph.run_rules(&[add_comm, add_assoc]).unwrap());

    // Fill the database.
    let mut ids = Vec::new();
    //  Add 0 .. N to the database.
    for i in 0..N {
        let i = egraph.primitives_mut().get(i as i64);
        ids.push(egraph.add_term(num_table, &[i], "base number"));
    }

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = egraph.add_term(add_table, &[*num, prev], "add_left");
            prev = id;
        }
        let left_root = prev;
        let mut prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter() {
            let id = egraph.add_term(add_table, &[prev, *num], "add_right");
            prev = id;
        }
        let right_root = prev;
        (left_root, right_root)
    };
    // Saturate
    while egraph.run_rules(&[add_comm, add_assoc]).unwrap() {}
    let canon_left = egraph.get_canon(left_root);
    let canon_right = egraph.get_canon(right_root);
    assert_eq!(canon_left, canon_right);
    let mut row = Vec::new();
    egraph.dump_table(add_table, |vals| {
        row.clear();
        row.extend_from_slice(vals);
    });

    let _term_explanation = egraph
        .explain_term(add_table, &row[0..row.len() - 1])
        .unwrap();
    _term_explanation.dump_explanation(&mut stderr()).unwrap();
}

#[test]
fn ac_fail() {
    const N: usize = 5;
    let mut egraph = EGraph::default();
    let int_prim = egraph.primitives_mut().get_ty::<i64>();
    let one = egraph.primitives_mut().get(1i64);
    let num_table = egraph.add_table(
        vec![ColumnTy::Primitive(int_prim), ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "num",
    );
    let add_table = egraph.add_table(
        vec![ColumnTy::Id; 3],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "add",
    );

    let add_comm = define_rule! {
        [egraph] ((-> (add_table x y) id) (-> (num_table {one}) x))
              => ((set (add_table y x) id))
    };

    let add_assoc = define_rule! {
        [egraph] ((-> (add_table x (add_table y z)) id))
              => ((set (add_table (add_table x y) z) id))
    };

    // Running these rules on an empty database should change nothing.
    assert!(!egraph.run_rules(&[add_comm, add_assoc]).unwrap());

    // Fill the database.
    let mut ids = Vec::new();
    //  Add 0 .. N to the database.
    let num_rows = (0..N)
        .map(|i| {
            let id = egraph.fresh_id();
            let i = egraph.primitives_mut().get(i as i64);
            ids.push(id);
            (num_table, vec![i, id])
        })
        .collect::<Vec<_>>();
    egraph.add_values(num_rows);

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut to_add = Vec::new();
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![*num, prev, id]));
            prev = id;
        }
        let left_root = to_add.last().unwrap().1[2];
        prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter() {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![prev, *num, id]));
            prev = id;
        }
        let right_root = to_add.last().unwrap().1[2];
        egraph.add_values(to_add);
        (left_root, right_root)
    };
    // Saturate
    while egraph.run_rules(&[add_comm, add_assoc]).unwrap() {}
    let canon_left = egraph.get_canon(left_root);
    let canon_right = egraph.get_canon(right_root);
    assert_ne!(canon_left, canon_right);
}

#[test]
fn math() {
    math_test(EGraph::default())
}

#[test]
fn math_tracing() {
    math_test(EGraph::with_tracing())
}

fn math_test(mut egraph: EGraph) {
    const N: usize = 8;
    let rational_ty = egraph.primitives_mut().get_ty::<Rational64>();
    let string_ty = egraph.primitives_mut().get_ty::<&'static str>();
    // tables
    let diff = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "diff",
    );
    let integral = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "integral",
    );
    let add = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "add",
    );
    let sub = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "sub",
    );
    let mul = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "mul",
    );
    let div = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "div",
    );
    let pow = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "pow",
    );

    let ln = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "ln",
    );
    let sqrt = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "sqrt",
    );
    let sin = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "sin",
    );
    let cos = egraph.add_table(
        vec![ColumnTy::Id, ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "cos",
    );
    let rat = egraph.add_table(
        vec![ColumnTy::Primitive(rational_ty), ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "rat",
    );
    let var = egraph.add_table(
        vec![ColumnTy::Primitive(string_ty), ColumnTy::Id],
        DefaultVal::FreshId,
        MergeFn::UnionId,
        "var",
    );

    let zero = egraph.primitives_mut().get(Rational64::new(0, 1));
    let one = egraph.primitives_mut().get(Rational64::new(1, 1));
    let neg1 = egraph.primitives_mut().get(Rational64::new(-1, 1));
    let two = egraph.primitives_mut().get(Rational64::new(2, 1));
    let three = egraph.primitives_mut().get(Rational64::new(3, 1));
    let seven = egraph.primitives_mut().get(Rational64::new(7, 1));
    let rules = [
        define_rule! {
            [egraph] ((-> (add x y) id)) => ((set (add y x) id))
        },
        define_rule! {
            [egraph] ((-> (mul x y) id)) => ((set (mul y x) id))
        },
        define_rule! {
            [egraph] ((-> (add x (add y z)) id)) => ((set (add (add x y) z) id))
        },
        define_rule! {
            [egraph] ((-> (mul x (mul y z)) id)) => ((set (mul (mul x y) z) id))
        },
        define_rule! {
            [egraph] ((-> (sub x y) id)) => ((set (add x (mul (rat {neg1}) y)) id))
        },
        define_rule! {
            [egraph] ((-> (add a (rat {zero})) id)) => ((union a id))
        },
        define_rule! {
            [egraph] ((-> (rat {zero}) z_id) (-> (mul a z_id) id))
                    => ((union id z_id))
        },
        define_rule! {
            [egraph] ((-> (mul a (rat {one})) id)) => ((union a id))
        },
        define_rule! {
            [egraph] ((-> (sub x x) id)) => ((union id (rat {zero})))
        },
        define_rule! {
            [egraph] ((-> (mul x (add b c)) id)) => ((set (add (mul x b) (mul x c)) id))
        },
        define_rule! {
            [egraph] ((-> (add (mul x a) (mul x b)) id)) => ((set (mul x (add a b)) id))
        },
        define_rule! {
            [egraph] ((-> (mul (pow a b) (pow a c)) id)) => ((set (pow a (add b c)) id))
        },
        define_rule! {
            [egraph] ((-> (pow x (rat {one})) id)) => ((union x id))
        },
        define_rule! {
            [egraph] ((-> (pow x (rat {two})) id)) => ((set (mul x x) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (add a b)) id)) => ((set (add (diff x a) (diff x b)) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (mul a b)) id)) => ((set (add (mul a (diff x b)) (mul b (diff x a))) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (sin x)) id)) => ((set (cos x) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (cos x)) id)) => ((set (mul (rat {neg1}) (sin x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (rat {one}) x) id)) => ((union id x))
        },
        define_rule! {
            [egraph] ((-> (integral (cos x) x) id)) => ((set (sin x) id))
        },
        define_rule! {
            [egraph] ((-> (integral (sin x) x) id)) => ((set (mul (rat {neg1}) (cos x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (add f g) x) id)) => ((set (add (integral f x) (integral g x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (sub f g) x) id)) => ((set (sub (integral f x) (integral g x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (mul a b) x) id))
            => ((set (sub (mul a (integral b x))
                          (integral (mul (diff x a) (integral b x)) x)) id))
        },
    ];
    let x_str = egraph.primitives_mut().get::<&'static str>("x");
    let y_str = egraph.primitives_mut().get::<&'static str>("y");
    let five_str = egraph.primitives_mut().get::<&'static str>("five");
    add_expressions! {
        [egraph]

        (integral (ln (var x_str)) (var x_str))
        (integral (add (var x_str) (cos (var x_str))) (var x_str))
        (integral (mul (cos (var x_str)) (var x_str)) (var x_str))
        (diff (var x_str)
            (add (rat one) (mul (rat two) (var x_str))))
        (diff (var x_str)
            (sub (pow (var x_str) (rat three)) (mul (rat seven) (pow (var x_str) (rat two)))))
        (add
            (mul (var y_str) (add (var x_str) (var y_str)))
            (sub (add (var x_str) (rat two)) (add (var x_str) (var x_str))))
        (div (rat one)
             (sub (div (add (rat one) (sqrt (var five_str))) (rat two))
                  (div (sub (rat one) (sqrt (var five_str))) (rat two))))
    }

    for _ in 0..N {
        if !egraph.run_rules(&rules).unwrap() {
            break;
        }
    }

    // numbers validated against the egglog implementation.

    assert_eq!(338, egraph.table_size(diff));
    assert_eq!(782, egraph.table_size(integral));
    assert_eq!(2977, egraph.table_size(add));
    assert_eq!(483, egraph.table_size(sub));
    assert_eq!(3516, egraph.table_size(mul));
    assert_eq!(3, egraph.table_size(div));
    assert_eq!(2, egraph.table_size(pow));
    assert_eq!(1, egraph.table_size(ln));
    assert_eq!(1, egraph.table_size(sqrt));
    assert_eq!(1, egraph.table_size(sin));
    assert_eq!(1, egraph.table_size(cos));
    assert_eq!(5, egraph.table_size(rat));
    assert_eq!(3, egraph.table_size(var));

    if egraph.tracing {
        let mut row = Vec::new();
        egraph.dump_table(mul, |vals| {
            row.clear();
            row.extend_from_slice(vals);
        });
        todo!("add proofs back")
    }
}

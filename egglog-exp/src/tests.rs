use bumpalo::Bump;

use crate::{
    actions::RuleId,
    common::{DenseIdMap, InternTable},
    define_id,
    free_join::Variable,
    function::Value,
    lift_operation,
    pool::{Clear, Pool, PoolSet},
    schema::{ColumnTy, Schema},
    Db,
};

define_id!(pub TestId, u32);

#[test]
fn interning_ints() {
    let mut table = InternTable::<usize, TestId>::default();
    let v1 = table.intern(&0);
    let v2 = table.intern(&1);
    let v3 = table.intern(&0);
    assert_eq!(v1, v3);
    assert_ne!(v1, v2);

    assert_eq!(table.get(v1), &0);
    assert_eq!(table.get(v2), &1);
}

#[test]
fn dense_ids_map() {
    let mut map = DenseIdMap::<TestId, usize>::new();
    map.insert(TestId::new(3), 1);
    assert_eq!(map.get(TestId::new(5)), None);
    assert_eq!(map.get(TestId::new(3)), Some(&1));
    assert_eq!(map.get_or_default(TestId::new(5)), &0);
}

#[test]
fn pool() {
    let pool = Pool::<Vec<usize>>::default();
    {
        let mut v1 = pool.get_default();
        v1.push(0);
        v1.push(1);
        assert_eq!(&*v1, &[0, 1]);
    }
    let v2 = pool.get_default();
    assert!(v2.is_empty());

    static mut DROPPED: bool = false;
    #[derive(Default)]
    struct Dropper;

    impl Clear for Dropper {
        type Factory = ();
        type Args<'a> = ();
        fn new(_: &()) -> Self {
            Dropper
        }
        fn clear(&mut self) {}
    }

    impl Drop for Dropper {
        fn drop(&mut self) {
            unsafe {
                DROPPED = true;
            }
        }
    }

    {
        let pool = Pool::<Dropper>::default();
        {
            let _ = pool.get_default();
        }

        unsafe {
            assert!(!DROPPED);
        }
    }
    unsafe {
        assert!(DROPPED);
    }
}

#[test]
fn pool_no_reuse() {
    static mut DROPPED: bool = false;
    #[derive(Default)]
    struct Dropper;

    impl Clear for Dropper {
        type Factory = ();
        type Args<'a> = ();
        fn new(_: &()) -> Self {
            Dropper
        }
        fn clear(&mut self) {}
        fn reuse(&self) -> bool {
            false
        }
    }

    impl Drop for Dropper {
        fn drop(&mut self) {
            unsafe {
                DROPPED = true;
            }
        }
    }

    let pool = Pool::<Dropper>::default();
    {
        let _ = pool.get_default();
    }

    unsafe {
        assert!(DROPPED);
    }
}

#[test]
fn basic_math() {
    const N: i64 = 100;
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let i64_ty = db.prims_mut().get_ty::<i64>();
    let add_i64 = lift_operation!([db.prims_mut()] fn add_i64(a: i64, b: i64) -> i64 {
        a + b
    });

    let num = db.declare_function(Schema::new(vec![ColumnTy::Primitive(i64_ty)], ColumnTy::Id));
    let add = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));

    let mut builder = db.query_builder();
    let x = builder.new_var("x", ColumnTy::Primitive(i64_ty));
    let x_id = builder.new_var("x_id", ColumnTy::Id);
    let y = builder.new_var("y", ColumnTy::Primitive(i64_ty));
    let y_id = builder.new_var("y_id", ColumnTy::Id);
    let add_id = builder.new_var("add_id", ColumnTy::Id);

    // ((= x_id (num x)) (= y_id (num y)) (= add_id (add x_id y_id)))

    builder.add_atom(num, &[x.into(), x_id.into()]);
    builder.add_atom(num, &[y.into(), y_id.into()]);
    builder.add_atom(add, &[x_id.into(), y_id.into(), add_id.into()]);

    let mut rule_builder = builder.rule().unwrap();
    let x_plus_y = rule_builder.prim(add_i64, &[x.into(), y.into()]).unwrap();
    let res_num = rule_builder
        .lookup_with_default(num, &[x_plus_y.into()])
        .unwrap();
    rule_builder.union(res_num, add_id).unwrap();

    let eval_add = rule_builder.finish();

    let mut constants = Vec::with_capacity(N as usize);

    for i in 0..N {
        constants.push(db.prims_mut().get::<i64>(i));
    }

    let mut add_data = db.standalone_rule();

    let zero = add_data
        .lookup_with_default(num, &[constants[0].into()])
        .unwrap();
    let mut prev = zero;
    for i in 1..N {
        let c = add_data
            .lookup_with_default(num, &[constants[i as usize].into()])
            .unwrap();
        prev = add_data
            .lookup_with_default(add, &[prev.into(), c.into()])
            .unwrap();
    }

    let add_data = add_data.finish();
    let mut root = Value::new(!0);
    let mut zero_v = Value::new(!0);

    db.run_rules_with(&[add_data], Default::default(), |_, bindings| {
        root = bindings[prev];
        zero_v = bindings[zero];
    });

    assert_ne!(root, Value::new(!0));

    let mut rounds = 0;
    while db.changed() {
        let mut matches = 0;
        db.run_rules_with(&[eval_add], Default::default(), |_, _| {
            matches += 1;
        });
        db.rebuild_all();
        rounds += 1;
        assert!(rounds < N * 2);
    }

    assert_eq!(rounds, N);

    let res = N * (N - 1) / 2;

    let res_val = db.prims_mut().get(res);

    let mut rule_builder = db.standalone_rule();
    let num_id_var = rule_builder.lookup(num, &[res_val.into()]).unwrap();
    let read_result = rule_builder.finish();

    let mut num_id = Value::new(!0);

    db.run_rules_with(&[read_result], Default::default(), |_, bindings| {
        num_id = bindings[num_id_var];
    });

    assert_eq!(db.canonicalize(root), num_id);
    assert_ne!(db.canonicalize(zero_v), num_id);
}

#[test]
fn ac_builtin_rebuild() {
    const N: i64 = 4;
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let i64_ty = db.prims_mut().get_ty::<i64>();

    let num = db.declare_function(Schema::new(vec![ColumnTy::Primitive(i64_ty)], ColumnTy::Id));
    let add = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));

    let add_comm = {
        let mut builder = db.query_builder();
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let add_id = builder.new_var("add_id", ColumnTy::Id);

        builder.add_atom(add, &[x_id.into(), y_id.into(), add_id.into()]);

        let mut rule_builder = builder.rule().unwrap();
        rule_builder
            .insert(add, &[y_id.into(), x_id.into()], add_id.into())
            .unwrap();
        rule_builder.finish()
    };

    let add_assoc = {
        let mut builder = db.query_builder();
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let z_id = builder.new_var("z_id", ColumnTy::Id);
        let y_plus_z = builder.new_var("y_plus_z", ColumnTy::Id);
        let root = builder.new_var("root", ColumnTy::Id);

        builder.add_atom(add, &[y_id.into(), z_id.into(), y_plus_z.into()]);
        builder.add_atom(add, &[x_id.into(), y_plus_z.into(), root.into()]);

        let mut rule_builder = builder.rule().unwrap();
        let x_plus_y = rule_builder
            .lookup_with_default(add, &[x_id.into(), y_id.into()])
            .unwrap();
        rule_builder
            .insert(add, &[x_plus_y.into(), z_id.into()], root.into())
            .unwrap();
        rule_builder.finish()
    };

    let (add_data, final_left, final_right) = {
        let mut constants = Vec::with_capacity(N as usize);

        for i in 0..N {
            constants.push(db.prims_mut().get::<i64>(i));
        }

        let mut add_data = db.standalone_rule();

        let zero = add_data
            .lookup_with_default(num, &[constants[0].into()])
            .unwrap();
        let mut prev = zero;
        for i in 1..N {
            let c = add_data
                .lookup_with_default(num, &[constants[i as usize].into()])
                .unwrap();
            prev = add_data
                .lookup_with_default(add, &[prev.into(), c.into()])
                .unwrap();
        }

        let final_left = prev;

        let max = add_data
            .lookup_with_default(num, &[constants[N as usize - 1].into()])
            .unwrap();
        prev = max;
        for i in (0..(N - 1)).rev() {
            let c = add_data
                .lookup_with_default(num, &[constants[i as usize].into()])
                .unwrap();
            prev = add_data
                .lookup_with_default(add, &[prev.into(), c.into()])
                .unwrap();
        }

        let final_right = prev;

        (add_data.finish(), final_left, final_right)
    };
    let mut left_root = Value::new(!0);
    let mut right_root = Value::new(!0);

    db.run_rules_with(&[add_data], Default::default(), |_, bindings| {
        left_root = bindings[final_left];
        right_root = bindings[final_right];
    });

    assert_ne!(left_root, Value::new(!0));
    assert_ne!(right_root, Value::new(!0));
    assert_ne!(right_root, left_root);

    while db.changed() {
        db.run_rules(&[add_comm, add_assoc]);
        db.rebuild_all();
    }

    assert_eq!(db.canonicalize(left_root), db.canonicalize(right_root));
}

#[test]
fn ac_manual_rebuild() {
    const N: i64 = 4;
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let i64_ty = db.prims_mut().get_ty::<i64>();
    let unit_ty = db.prims_mut().get_ty::<()>();
    let unit_val = db.prims_mut().get(());

    let num = db.declare_function(Schema::new(vec![ColumnTy::Primitive(i64_ty)], ColumnTy::Id));
    let add = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let parent = db.declare_function(Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Primitive(unit_ty),
    ));

    let num_refl = {
        // (= (num n) n_id) => (parent n_id n_id)
        let mut builder = db.query_builder();
        let n = builder.new_var("n", ColumnTy::Primitive(i64_ty));
        let n_id = builder.new_var("n_id", ColumnTy::Id);
        builder.add_atom(num, &[n.into(), n_id.into()]);
        let mut rule_builder = builder.rule().unwrap();
        rule_builder
            .insert(parent, &[n_id.into(), n_id.into()], unit_val.into())
            .unwrap();
        rule_builder.finish()
    };

    let add_refl = {
        // (= (add x y) x_plus_y_id) => (parent x_plus_y_id x_plus_y_id)
        let mut builder = db.query_builder();
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let x_plus_y_id = builder.new_var("x_plus_y_id", ColumnTy::Id);
        builder.add_atom(add, &[x_id.into(), y_id.into(), x_plus_y_id.into()]);
        let mut rule_builder = builder.rule().unwrap();
        rule_builder
            .insert(
                parent,
                &[x_plus_y_id.into(), x_plus_y_id.into()],
                unit_val.into(),
            )
            .unwrap();
        rule_builder.finish()
    };

    let parent_trans = {
        // (parent a b) (parent b c) => (parent a c) (delete (parent a b))
        let mut builder = db.query_builder();
        let a = builder.new_var("a", ColumnTy::Id);
        let b = builder.new_var("b", ColumnTy::Id);
        let c = builder.new_var("c", ColumnTy::Id);
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));

        builder.add_atom(parent, &[a.into(), b.into(), u.into()]);
        builder.add_atom(parent, &[b.into(), c.into(), u.into()]);
        let mut rule_builder = builder.rule().unwrap();
        rule_builder.assert_ne(a.into(), c.into()).unwrap();
        rule_builder.assert_ne(b.into(), c.into()).unwrap();
        rule_builder.assert_ne(a.into(), b.into()).unwrap();
        rule_builder
            .insert(parent, &[a.into(), c.into()], unit_val.into())
            .unwrap();
        rule_builder.remove(parent, &[a.into(), b.into()]).unwrap();
        rule_builder.finish()
    };

    let parent_sub = {
        // (parent a a) (parent a b) where a != b => (delete (parent a a))
        let mut builder = db.query_builder();
        let a = builder.new_var("a", ColumnTy::Id);
        let b = builder.new_var("b", ColumnTy::Id);
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));

        builder.add_atom(parent, &[a.into(), b.into(), u.into()]);
        builder.add_atom(parent, &[a.into(), a.into(), u.into()]);
        let mut rule_builder = builder.rule().unwrap();
        rule_builder.assert_ne(a.into(), b.into()).unwrap();
        rule_builder.remove(parent, &[a.into(), a.into()]).unwrap();
        rule_builder.finish()
    };

    let parent_acyclic = {
        // (parent a b) (parent b a) where (!= b a)
        // =>
        // (let (child parent) (tiebreak a b))
        // (delete (parent a b))
        // (delete (parent b a))
        // (parent child parent)
        let mut builder = db.query_builder();
        let a = builder.new_var("a", ColumnTy::Id);
        let b = builder.new_var("b", ColumnTy::Id);
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));

        builder.add_atom(parent, &[a.into(), b.into(), u.into()]);
        builder.add_atom(parent, &[b.into(), a.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        rule_builder.assert_ne(a.into(), b.into()).unwrap();
        let (child, canon) = rule_builder.tie_break(a, b).unwrap();
        rule_builder
            .remove(parent, &[canon.into(), child.into()])
            .unwrap();
        rule_builder
            .insert(parent, &[child.into(), canon.into()], unit_val.into())
            .unwrap();
        rule_builder.finish()
    };

    let parent_canon = {
        let mut builder = db.query_builder();
        let a = builder.new_var("a", ColumnTy::Id);
        let b = builder.new_var("b", ColumnTy::Id);
        let c = builder.new_var("c", ColumnTy::Id);
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));

        builder.add_atom(parent, &[a.into(), b.into(), u.into()]);
        builder.add_atom(parent, &[a.into(), c.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        rule_builder.assert_ne(a.into(), b.into()).unwrap();
        rule_builder.assert_ne(a.into(), c.into()).unwrap();
        rule_builder.assert_ne(b.into(), c.into()).unwrap();
        let (child, canon) = rule_builder.tie_break(b, c).unwrap();
        rule_builder
            .insert(parent, &[child.into(), canon.into()], unit_val.into())
            .unwrap();
        rule_builder.finish()
    };

    let add_canon_left = {
        // (= z (add x y)) (parent x x_parent) (parent z z_parent) where (!= x x_parent)
        // => (let new_parent (add x_parent y)) (parent new_parent z_parent)
        let mut builder = db.query_builder();
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let x_parent = builder.new_var("x_parent", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let z_id = builder.new_var("z_id", ColumnTy::Id);
        let z_parent = builder.new_var("z_parent", ColumnTy::Id);

        builder.add_atom(add, &[x_id.into(), y_id.into(), z_id.into()]);
        builder.add_atom(parent, &[x_id.into(), x_parent.into(), u.into()]);
        builder.add_atom(parent, &[z_id.into(), z_parent.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        rule_builder
            .assert_ne(x_id.into(), x_parent.into())
            .unwrap();
        let new_parent = rule_builder
            .lookup_with_default(add, &[x_parent.into(), y_id.into()])
            .unwrap();
        rule_builder
            .insert(
                parent,
                &[new_parent.into(), z_parent.into()],
                unit_val.into(),
            )
            .unwrap();
        rule_builder.finish()
    };

    let add_canon_right = {
        // (= z (add x y)) (parent x x) (parent y y_parent) (parent z z_parent) where (!= y y_parent)
        // => (let new_parent (add x y_parent)) (parent new_parent z_parent)
        let mut builder = db.query_builder();
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let y_parent = builder.new_var("y_parent", ColumnTy::Id);
        let z_id = builder.new_var("z_id", ColumnTy::Id);
        let z_parent = builder.new_var("z_parent", ColumnTy::Id);

        builder.add_atom(add, &[x_id.into(), y_id.into(), z_id.into()]);
        builder.add_atom(parent, &[x_id.into(), x_id.into(), u.into()]);
        builder.add_atom(parent, &[y_id.into(), y_parent.into(), u.into()]);
        builder.add_atom(parent, &[z_id.into(), z_parent.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        rule_builder
            .assert_ne(y_id.into(), y_parent.into())
            .unwrap();
        let new_parent = rule_builder
            .lookup_with_default(add, &[x_id.into(), y_parent.into()])
            .unwrap();
        rule_builder
            .insert(
                parent,
                &[new_parent.into(), z_parent.into()],
                unit_val.into(),
            )
            .unwrap();
        rule_builder.finish()
    };

    let add_comm = {
        // (= z (add x y)) (parent x x) (parent y y) (parent z z_parent)
        // =>
        // (let new_parent (add y x))
        // (parent new_parent z_parent)
        let mut builder = db.query_builder();
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));
        let add_id = builder.new_var("add_id", ColumnTy::Id);
        let add_parent = builder.new_var("add_parent", ColumnTy::Id);

        builder.add_atom(add, &[x_id.into(), y_id.into(), add_id.into()]);
        builder.add_atom(parent, &[x_id.into(), x_id.into(), u.into()]);
        builder.add_atom(parent, &[add_id.into(), add_parent.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        let new_id = rule_builder
            .lookup_with_default(add, &[y_id.into(), x_id.into()])
            .unwrap();
        rule_builder
            .insert(parent, &[new_id.into(), add_parent.into()], u.into())
            .unwrap();
        rule_builder.finish()
    };

    let add_assoc = {
        // (= inter (add y z)) (= root (add x i')) (parent inter i') (parent root root')
        // (parent x x) (parent y y) (parent z z)
        // =>
        // (let new_inter (add x y))
        // (let new_root (add new_inter z))
        // (parent new_root root')
        let mut builder = db.query_builder();
        let u = builder.new_var("u", ColumnTy::Primitive(unit_ty));
        let x_id = builder.new_var("x_id", ColumnTy::Id);
        let y_id = builder.new_var("y_id", ColumnTy::Id);
        let z_id = builder.new_var("z_id", ColumnTy::Id);
        let inter = builder.new_var("inter", ColumnTy::Id);
        let inter_p = builder.new_var("inter_p", ColumnTy::Id);
        let root = builder.new_var("root", ColumnTy::Id);
        let root_p = builder.new_var("root_p", ColumnTy::Id);

        builder.add_atom(add, &[y_id.into(), z_id.into(), inter.into()]);
        builder.add_atom(add, &[x_id.into(), inter_p.into(), root.into()]);

        builder.add_atom(parent, &[inter.into(), inter_p.into(), u.into()]);
        builder.add_atom(parent, &[x_id.into(), x_id.into(), u.into()]);
        builder.add_atom(parent, &[y_id.into(), y_id.into(), u.into()]);
        builder.add_atom(parent, &[z_id.into(), z_id.into(), u.into()]);
        builder.add_atom(parent, &[root.into(), root_p.into(), u.into()]);

        let mut rule_builder = builder.rule().unwrap();
        let new_inter = rule_builder
            .lookup_with_default(add, &[x_id.into(), y_id.into()])
            .unwrap();
        let new_root = rule_builder
            .lookup_with_default(add, &[new_inter.into(), z_id.into()])
            .unwrap();
        rule_builder
            .insert(parent, &[new_root.into(), root_p.into()], u.into())
            .unwrap();
        rule_builder.finish()
    };

    let (add_data, final_left, final_right) = {
        let mut constants = Vec::with_capacity(N as usize);

        for i in 0..N {
            constants.push(db.prims_mut().get::<i64>(i));
        }

        let mut add_data = db.standalone_rule();

        let zero = add_data
            .lookup_with_default(num, &[constants[0].into()])
            .unwrap();
        let mut prev = zero;
        for i in 1..N {
            let c = add_data
                .lookup_with_default(num, &[constants[i as usize].into()])
                .unwrap();
            prev = add_data
                .lookup_with_default(add, &[prev.into(), c.into()])
                .unwrap();
        }

        let final_left = prev;

        let max = add_data
            .lookup_with_default(num, &[constants[N as usize - 1].into()])
            .unwrap();
        prev = max;
        for i in (0..(N - 1)).rev() {
            let c = add_data
                .lookup_with_default(num, &[constants[i as usize].into()])
                .unwrap();
            prev = add_data
                .lookup_with_default(add, &[prev.into(), c.into()])
                .unwrap();
        }

        let final_right = prev;

        (add_data.finish(), final_left, final_right)
    };
    let mut left_root = Value::new(!0);
    let mut right_root = Value::new(!0);

    db.run_rules_with(&[add_data], Default::default(), |_, bindings| {
        left_root = bindings[final_left];
        right_root = bindings[final_right];
    });

    assert_ne!(left_root, Value::new(!0));
    assert_ne!(right_root, Value::new(!0));
    assert_ne!(right_root, left_root);

    eprintln!("left_root={left_root:?}");
    eprintln!("right_root={right_root:?}");

    let repair_once = [num_refl, add_refl];
    let repair_uf = [parent_canon, parent_sub, parent_acyclic, parent_trans];
    let repair_add = [add_canon_left, add_canon_right];
    let main_rules = [add_comm, add_assoc];

    while db.changed() {
        db.run_rules(&repair_once);
        let mut inner = true;
        while inner {
            inner = false;
            saturate(&mut db, &[parent_acyclic]);
            for rule in repair_uf.iter().copied() {
                db.run_rules(&[rule]);
                inner |= db.changed();
            }
        }
        saturate(&mut db, &repair_add);
        db.run_rules(&main_rules);
    }
    db.run_rules(&repair_once);
    saturate(&mut db, &repair_add);
    saturate(&mut db, &repair_uf);

    let mut left_canon = Value::new(!0);
    let mut right_canon = Value::new(!0);

    {
        // Now read the parents out
        let mut builder = db.query_builder();
        let left = builder.new_var("left", ColumnTy::Id);
        let right = builder.new_var("right", ColumnTy::Id);
        builder.add_atom(parent, &[left_root.into(), left.into(), unit_val.into()]);
        builder.add_atom(parent, &[right_root.into(), right.into(), unit_val.into()]);
        let read_canon = builder.rule().unwrap().finish();
        db.run_rules_with(&[read_canon], Default::default(), |_, bindings| {
            // This should only run once
            assert_eq!(left_canon, Value::new(!0));
            left_canon = bindings[left];
            right_canon = bindings[right];
        });
    }

    assert_ne!(left_canon, Value::new(!0));
    assert_eq!(left_canon, right_canon);
}

fn saturate(db: &mut Db, rules: &[RuleId]) {
    saturate_with(db, rules, |_, _| {})
}
fn saturate_with(
    db: &mut Db,
    rules: &[RuleId],
    mut cb: impl FnMut(RuleId, &DenseIdMap<Variable, Value>),
) {
    db.run_rules_with(rules, Default::default(), &mut cb);
    while db.changed() {
        db.run_rules_with(rules, Default::default(), &mut cb);
    }
}

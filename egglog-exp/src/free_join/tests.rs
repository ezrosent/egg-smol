use bumpalo::Bump;
use smallvec::smallvec;

use crate::{
    common::NumericId,
    free_join::{
        execute::{Runner, TimestampRange},
        plan::{JoinStage, Plan, PlanStrategy, ScanSpec},
        AtomId, AtomIdx, QueryEntry, SubAtom, Variable,
    },
    function::{index_cache::IndexCache, table::Timestamp, Value},
    pool::PoolSet,
    schema::{ColumnTy, Schema},
    Db,
};

use JoinStage::Intersect;

#[test]
fn basic_plan() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f0 = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let f1 = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let mut builder = db.query_builder();
    // F(x, y), G(y, z)
    let x = builder.new_var("x", ColumnTy::Id);
    let y = builder.new_var("y", ColumnTy::Id);
    let z = builder.new_var("z", ColumnTy::Id);
    let a1 = builder.add_atom_with_id(f0, &[x.into(), y.into()]);
    let a2 = builder.add_atom_with_id(f1, &[y.into(), z.into()]);
    let query = builder.build().unwrap();
    let plan1 = query.plan(PlanStrategy::PureSize, vec![(a1, 5), (a2, 4)]);
    assert_eq!(
        plan1,
        Plan {
            stages: vec![
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(1),
                            vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![
                        (AtomIdx::new(0), Variable::new(1)),
                        (AtomIdx::new(1), Variable::new(2))
                    ],
                    to_intersect: vec![(
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(0),
                                vars: smallvec![AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(0)],
                    )],
                },
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(0),
                            vars: smallvec![AtomIdx::new(0)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![(AtomIdx::new(0), Variable::new(0))],
                    to_intersect: vec![],
                },
            ],
        }
    );

    // Swap variable orders when the atoms change relative size.

    let plan2 = query.plan(PlanStrategy::PureSize, vec![(a1, 2), (a2, 5)]);
    assert_eq!(
        plan2,
        Plan {
            stages: vec![
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(0),
                            vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![
                        (AtomIdx::new(0), Variable::new(0)),
                        (AtomIdx::new(1), Variable::new(1))
                    ],
                    to_intersect: vec![(
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(1),
                                vars: smallvec![AtomIdx::new(0)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(1)],
                    )],
                },
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(1),
                            vars: smallvec![AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![(AtomIdx::new(1), Variable::new(2))],
                    to_intersect: vec![],
                },
            ],
        }
    );
}

#[test]
fn basic_plan_mincover() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f0 = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let f1 = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let mut builder = db.query_builder();
    // F(x, y), G(y, z)
    let x = builder.new_var("x", ColumnTy::Id);
    let y = builder.new_var("y", ColumnTy::Id);
    let z = builder.new_var("z", ColumnTy::Id);
    let a1 = builder.add_atom_with_id(f0, &[x.into(), y.into()]);
    let a2 = builder.add_atom_with_id(f1, &[y.into(), z.into()]);
    let query = builder.build().unwrap();
    let plan1 = query.plan(PlanStrategy::MinCover, vec![(a1, 5), (a2, 4)]);
    assert_eq!(
        plan1,
        Plan {
            stages: vec![
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(1),
                            vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![
                        (AtomIdx::new(0), Variable::new(1)),
                        (AtomIdx::new(1), Variable::new(2))
                    ],
                    to_intersect: vec![(
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(0),
                                vars: smallvec![AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(0)],
                    )],
                },
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(0),
                            vars: smallvec![AtomIdx::new(0)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![(AtomIdx::new(0), Variable::new(0))],
                    to_intersect: vec![],
                },
            ],
        }
    );

    // Swap variable orders when the atoms change relative size.

    let plan2 = query.plan(PlanStrategy::MinCover, vec![(a1, 2), (a2, 5)]);
    assert_eq!(
        plan2,
        Plan {
            stages: vec![
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(0),
                            vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![
                        (AtomIdx::new(0), Variable::new(0)),
                        (AtomIdx::new(1), Variable::new(1))
                    ],
                    to_intersect: vec![(
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(1),
                                vars: smallvec![AtomIdx::new(0)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(1)],
                    )],
                },
                Intersect {
                    cover: ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(1),
                            vars: smallvec![AtomIdx::new(1)],
                        },
                        constrain_eq: vec![],
                    },
                    bind: smallvec![(AtomIdx::new(1), Variable::new(2))],
                    to_intersect: vec![],
                },
            ],
        }
    );
}

#[test]
fn complex_query_mincover() {
    // F(x, x, y => z), F(x, y, a => w), G(y => w), H(z, a => b)
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f = db.declare_function(Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Id,
    ));
    let g = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let h = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let mut builder = db.query_builder();
    let vx = builder.new_var("x", ColumnTy::Id);
    let vy = builder.new_var("y", ColumnTy::Id);
    let vz = builder.new_var("z", ColumnTy::Id);
    let vw = builder.new_var("w", ColumnTy::Id);
    let va = builder.new_var("a", ColumnTy::Id);
    let vb = builder.new_var("b", ColumnTy::Id);
    let a1 = builder.add_atom_with_id(f, &[vx.into(), vx.into(), vy.into(), vz.into()]);
    let a2 = builder.add_atom_with_id(f, &[vx.into(), vy.into(), va.into(), vw.into()]);
    let a3 = builder.add_atom_with_id(g, &[vy.into(), vw.into()]);
    let a4 = builder.add_atom_with_id(h, &[vz.into(), va.into(), vb.into()]);
    let query = builder.build().unwrap();
    let plan = query.plan(
        PlanStrategy::MinCover,
        vec![(a1, 6), (a2, 6), (a3, 4), (a4, 4)],
    );
    let expected = Plan {
        stages: vec![
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(3),
                        vars: smallvec![AtomIdx::new(0), AtomIdx::new(1), AtomIdx::new(2)],
                    },
                    constrain_eq: vec![],
                },
                bind: smallvec![
                    (AtomIdx::new(0), Variable::new(2)),
                    (AtomIdx::new(1), Variable::new(4)),
                    (AtomIdx::new(2), Variable::new(5)),
                ],
                to_intersect: vec![
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(0),
                                vars: smallvec![AtomIdx::new(3)],
                            },
                            constrain_eq: vec![(AtomIdx::new(0), AtomIdx::new(1))],
                        },
                        smallvec![AtomIdx::new(0)],
                    ),
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(1),
                                vars: smallvec![AtomIdx::new(2)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(1)],
                    ),
                ],
            },
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(1),
                        vars: smallvec![AtomIdx::new(0), AtomIdx::new(1), AtomIdx::new(3)],
                    },
                    constrain_eq: vec![],
                },
                bind: smallvec![
                    (AtomIdx::new(0), Variable::new(0)),
                    (AtomIdx::new(1), Variable::new(1)),
                    (AtomIdx::new(3), Variable::new(3)),
                ],
                to_intersect: vec![
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(0),
                                vars: smallvec![AtomIdx::new(0), AtomIdx::new(1), AtomIdx::new(2)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(0), AtomIdx::new(0), AtomIdx::new(1)],
                    ),
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(2),
                                vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(1), AtomIdx::new(3)],
                    ),
                ],
            },
        ],
    };
    assert_eq!(plan, expected);
}

#[test]
fn multiple_variables_plan() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let g = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let h = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let j = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let mut builder = db.query_builder();
    // F(x, y, z), G(x, y), H(y, z), J(x, z, w)
    let w = builder.new_var("w", ColumnTy::Id);
    let x = builder.new_var("x", ColumnTy::Id);
    let y = builder.new_var("y", ColumnTy::Id);
    let z = builder.new_var("z", ColumnTy::Id);
    let a1 = builder.add_atom_with_id(f, &[x.into(), y.into(), z.into()]);
    let a2 = builder.add_atom_with_id(g, &[x.into(), y.into()]);
    let a3 = builder.add_atom_with_id(h, &[y.into(), z.into()]);
    let a4 = builder.add_atom_with_id(j, &[x.into(), z.into(), w.into()]);

    let query = builder.build().unwrap();

    let plan = query.plan(
        PlanStrategy::PureSize,
        vec![(a1, 1), (a2, 4), (a3, 3), (a4, 5)],
    );
    let expected = Plan {
        stages: vec![
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(0),
                        vars: smallvec![AtomIdx::new(0), AtomIdx::new(1), AtomIdx::new(2)],
                    },
                    constrain_eq: vec![],
                },
                bind: smallvec![
                    (AtomIdx::new(0), Variable::new(1)),
                    (AtomIdx::new(1), Variable::new(2)),
                    (AtomIdx::new(2), Variable::new(3)),
                ],
                to_intersect: vec![
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(1),
                                vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                    ),
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(2),
                                vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(1), AtomIdx::new(2)],
                    ),
                    (
                        ScanSpec {
                            to_index: SubAtom {
                                atom: AtomId::new(3),
                                vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                            },
                            constrain_eq: vec![],
                        },
                        smallvec![AtomIdx::new(0), AtomIdx::new(2)],
                    ),
                ],
            },
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(3),
                        vars: smallvec![AtomIdx::new(2)],
                    },
                    constrain_eq: vec![],
                },
                bind: smallvec![(AtomIdx::new(2), Variable::new(0))],
                to_intersect: vec![],
            },
        ],
    };
    assert_eq!(plan, expected);
}

#[test]
fn intra_atom_equality_constraints_plan() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let g = db.declare_function(Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Id,
    ));
    let mut builder = db.query_builder();
    // F(x, x, y), G(y, z, z, y)
    let x = builder.new_var("x", ColumnTy::Id);
    let y = builder.new_var("y", ColumnTy::Id);
    let z = builder.new_var("z", ColumnTy::Id);
    let a1 = builder.add_atom_with_id(f, &[x.into(), x.into(), y.into()]);
    let a2 = builder.add_atom_with_id(g, &[y.into(), z.into(), z.into(), y.into()]);
    let query = builder.build().unwrap();
    let plan = query.plan(PlanStrategy::PureSize, vec![(a1, 5), (a2, 4)]);
    let expected = Plan {
        stages: vec![
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(1),
                        vars: smallvec![AtomIdx::new(0), AtomIdx::new(1)],
                    },
                    constrain_eq: vec![
                        (AtomIdx::new(0), AtomIdx::new(3)),
                        (AtomIdx::new(1), AtomIdx::new(2)),
                    ],
                },
                bind: smallvec![
                    (AtomIdx::new(3), Variable::new(1)),
                    (AtomIdx::new(2), Variable::new(2))
                ],
                to_intersect: vec![(
                    ScanSpec {
                        to_index: SubAtom {
                            atom: AtomId::new(0),
                            vars: smallvec![AtomIdx::new(2)],
                        },
                        constrain_eq: vec![(AtomIdx::new(0), AtomIdx::new(1))],
                    },
                    smallvec![AtomIdx::new(3)],
                )],
            },
            Intersect {
                cover: ScanSpec {
                    to_index: SubAtom {
                        atom: AtomId::new(0),
                        vars: smallvec![AtomIdx::new(0)],
                    },
                    constrain_eq: vec![],
                },
                bind: smallvec![(AtomIdx::new(1), Variable::new(0))],
                to_intersect: vec![],
            },
        ],
    };
    assert_eq!(plan, expected);
}

fn v(x: usize) -> Value {
    Value::from_usize(x)
}

fn ts(x: usize) -> Timestamp {
    Timestamp::from_usize(x)
}

#[test]
fn execute_edge_lookup() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f1 = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));

    let f2 = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    const N: usize = 200;
    // F1(x, y => z), F2(x => z)
    for i in 0..N {
        db.insert(f1, &[v(i), v(i + 1)], v(i + 2));
        db.insert(f2, &[v(i)], v(i + 1));
    }
    db.inc_timestamp();
    for i in 0..N {
        db.insert(f1, &[v(i), v(i + 2)], v(i + 1));
        db.insert(f1, &[v(i), v(i + 3)], v(i + 3));
    }

    let mut builder = db.query_builder();
    let vx = builder.new_var("x", ColumnTy::Id);
    let vy = builder.new_var("y", ColumnTy::Id);
    let vz = builder.new_var("z", ColumnTy::Id);
    builder.add_atom(f1, &[vx.into(), vy.into(), vz.into()]);
    builder.add_atom(f2, &[vx.into(), vz.into()]);
    let query = builder.build().unwrap();
    let mut index_cache = IndexCache::new(&pool_set);
    let mut run = Runner::new(
        TimestampRange {
            low: ts(0),
            high: ts(2),
        },
        PlanStrategy::default(),
        db.funcs(),
        &mut index_cache,
        &pool_set,
    );
    let mut results = Vec::new();
    run.run(&query, |bindings| {
        assert_eq!(bindings.n_ids(), 3);
        results.push((bindings[vx], bindings[vy], bindings[vz]));
    });
    assert_eq!(results.len(), N);
    results.sort();
    let mut expected = Vec::new();
    for i in 0..N {
        expected.push((v(i), v(i + 2), v(i + 1)));
    }
    assert_eq!(results, expected);
}

#[test]
fn execute_constant_edge_lookup() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f1 = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    let f2 = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    const N: usize = 200;
    // F1(x, y => z), F2(N*2, x => z)
    for i in 0..N {
        db.insert(f1, &[v(i), v(i + 1)], v(i + 2));
        db.insert(f2, &[v(N * 2), v(i)], v(i + 2));
        db.insert(f2, &[v(N * 2 + 1), v(i)], v(i + 2));
    }

    {
        let mut builder = db.query_builder();
        let vx = builder.new_var("x", ColumnTy::Id);
        let vy = builder.new_var("y", ColumnTy::Id);
        let vz = builder.new_var("z", ColumnTy::Id);
        builder.add_atom(f1, &[vx.into(), vy.into(), vz.into()]);
        builder.add_atom(f2, &[QueryEntry::Const(v(N * 2)), vx.into(), vz.into()]);
        let query = builder.build().unwrap();
        let mut index_cache = IndexCache::new(&pool_set);
        let mut run = Runner::new(
            TimestampRange {
                low: ts(0),
                high: ts(2),
            },
            PlanStrategy::default(),
            db.funcs(),
            &mut index_cache,
            &pool_set,
        );
        let mut results = Vec::new();
        run.run(&query, |bindings| {
            assert_eq!(bindings.n_ids(), 3);
            results.push((bindings[vx], bindings[vy], bindings[vz]));
        });
        assert_eq!(results.len(), N);
        results.sort();
        let mut expected = Vec::new();
        for i in 0..N {
            expected.push((v(i), v(i + 1), v(i + 2)));
        }
        assert_eq!(results, expected);
    }
    {
        // Constrain by a constant that isn't in the table.
        let mut builder = db.query_builder();
        let vx = builder.new_var("x", ColumnTy::Id);
        let vy = builder.new_var("y", ColumnTy::Id);
        let vz = builder.new_var("z", ColumnTy::Id);
        builder.add_atom(f1, &[vx.into(), vy.into(), vz.into()]);
        builder.add_atom(f2, &[QueryEntry::Const(v(N * 2 + 2)), vx.into(), vz.into()]);
        let query = builder.build().unwrap();
        let mut index_cache = IndexCache::new(&pool_set);
        let mut run = Runner::new(
            TimestampRange {
                low: ts(0),
                high: ts(2),
            },
            PlanStrategy::default(),
            db.funcs(),
            &mut index_cache,
            &pool_set,
        );
        let mut results = Vec::new();
        run.run(&query, |bindings| {
            assert_eq!(bindings.n_ids(), 3);
            results.push((bindings[vx], bindings[vy], bindings[vz]));
        });
        assert!(results.is_empty());
    }
}

#[test]
fn complex_nested_query() {
    let bump = Bump::new();
    let pool_set = PoolSet::new(&bump);
    let mut db = Db::new(&pool_set);
    let f = db.declare_function(Schema::new(
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Id,
    ));
    let g = db.declare_function(Schema::new(vec![ColumnTy::Id], ColumnTy::Id));
    let h = db.declare_function(Schema::new(vec![ColumnTy::Id, ColumnTy::Id], ColumnTy::Id));
    // F(x, x, y => z), F(x, y, a => w), G(y => w), H(z, a => b)
    const N: usize = 200;
    for i in 0..N {
        // Should match x=i, y=i+3, z=i+3, a=i, b=i+1, w=i+1
        db.insert(f, &[v(i), v(N + i + 1), v(i + 3)], v(i + 2));
        db.insert(f, &[v(i), v(i), v(i + 3)], v(i + 3));
        db.insert(f, &[v(i), v(i + 3), v(i)], v(i + 1));
        db.insert(g, &[v(i + 3)], v(i + 1));
        // With this line removed, the planner picks 'g' as the first cover and
        // the join seems to execute slower. Could be a good target for testing
        // adaptive reordering.
        db.insert(g, &[v(i + 2 * N)], v(i + N));
        db.insert(h, &[v(i + 3), v(i)], v(i + 1));
        db.insert(h, &[v(i + 3), v(i + 3)], v(i + 2));
    }

    let mut builder = db.query_builder();
    let vx = builder.new_var("x", ColumnTy::Id);
    let vy = builder.new_var("y", ColumnTy::Id);
    let vz = builder.new_var("z", ColumnTy::Id);
    let vw = builder.new_var("w", ColumnTy::Id);
    let va = builder.new_var("a", ColumnTy::Id);
    let vb = builder.new_var("b", ColumnTy::Id);
    builder.add_atom(f, &[vx.into(), vx.into(), vy.into(), vz.into()]);
    builder.add_atom(f, &[vx.into(), vy.into(), va.into(), vw.into()]);
    builder.add_atom(g, &[vy.into(), vw.into()]);
    builder.add_atom(h, &[vz.into(), va.into(), vb.into()]);
    let query = builder.build().unwrap();
    let mut index_cache = IndexCache::new(&pool_set);
    let mut run = Runner::new(
        TimestampRange {
            low: ts(0),
            high: ts(1),
        },
        PlanStrategy::default(),
        db.funcs(),
        &mut index_cache,
        &pool_set,
    );
    let mut results = Vec::new();
    run.run(&query, |bindings| {
        assert_eq!(bindings.n_ids(), 6);
        results.push((
            bindings[vx],
            bindings[vy],
            bindings[vz],
            bindings[va],
            bindings[vb],
            bindings[vw],
        ));
    });
    assert_eq!(results.len(), N, "just got {results:?}");
    results.sort();
    let mut expected = Vec::new();
    for i in 0..N {
        expected.push((v(i), v(i + 3), v(i + 3), v(i), v(i + 1), v(i + 1)));
    }
    assert_eq!(results, expected);
}

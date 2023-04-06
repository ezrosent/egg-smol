use petgraph::dot::Dot;

use crate::{
    choose_nodes, egraph::render_zdd, extract_greedy, extract_zdd, Egraph, Report, Zdd, ZddPool,
};

#[test]
fn basic_merge() {
    let pool = ZddPool::with_cache_size(1 << 20);
    let mut s1 = Zdd::with_pool(pool);
    s1.add(vec![1, 2, 3, 4, 5]);
    s1.add(vec![1, 2, 4, 5]);
    s1.add(vec![1, 2, 4, 5, 7]);
    s1.add(vec![2, 4, 5, 7]);
    let mut results = vec![];
    s1.for_each(|elts| {
        results.push(Vec::from_iter(elts.iter().copied()));
    });
    results.sort();
    assert_eq!(
        results,
        vec![
            vec![1, 2, 3, 4, 5],
            vec![1, 2, 4, 5],
            vec![1, 2, 4, 5, 7],
            vec![2, 4, 5, 7],
        ]
    );
}

#[test]
fn basic_min_cost() {
    let pool = ZddPool::with_cache_size(1 << 20);
    let mut s1 = Zdd::with_pool(pool);
    s1.add(vec![1, 2, 3, 4, 5]);
    s1.add(vec![1, 2, 4, 5]);
    s1.add(vec![1, 2, 4, 5, 7]);
    s1.add(vec![2, 4, 5, 7]);
    let (set, cost) = s1
        .min_cost_set(|x| *x as usize)
        .expect("there should be a solution");
    assert_eq!(cost, 12);
    assert_eq!(set, vec![1, 2, 4, 5]);
}

#[test]
fn basic_intersect() {
    let pool = ZddPool::with_cache_size(1 << 20);
    let mut s1 = Zdd::with_pool(pool.clone());
    let mut s2 = Zdd::with_pool(pool);

    s1.add(vec![1, 2, 3, 4, 5]);
    s1.add(vec![1, 2, 4, 5]);
    s1.add(vec![1, 2, 4, 5, 7]);
    s1.add(vec![2, 4, 5, 7]);

    s2.add(vec![1, 2, 3, 4, 5]);
    s2.add(vec![1, 3, 4, 5]);
    s2.add(vec![1, 3, 4, 5, 7]);
    s2.add(vec![2, 4, 5, 7]);

    s1.intersect(&s2);
    let mut results = vec![];
    s1.for_each(|elts| {
        results.push(Vec::from_iter(elts.iter().copied()));
    });
    results.sort();
    assert_eq!(results, vec![vec![1, 2, 3, 4, 5], vec![2, 4, 5, 7]]);
}

#[test]
fn basic_join() {
    let pool = ZddPool::with_cache_size(1 << 20);
    let mut s1 = Zdd::with_pool(pool.clone());
    let mut s2 = Zdd::with_pool(pool);

    s1.add(vec![1, 2]);
    s1.add(vec![6, 8]);

    s2.add(vec![3, 4, 5]);
    s2.add(vec![5, 6, 7]);

    s1.join(&s2);
    let mut results = vec![];
    s1.for_each(|elts| {
        results.push(Vec::from_iter(elts.iter().copied()));
    });
    results.sort();
    assert_eq!(
        results,
        vec![
            vec![1, 2, 3, 4, 5],
            vec![1, 2, 5, 6, 7],
            vec![3, 4, 5, 6, 8],
            vec![5, 6, 7, 8],
        ]
    );
}

struct FakeEgraph {
    nodes: Vec<(Vec<usize>, usize)>,
    classes: Vec<Vec<usize>>,
}

impl Egraph for FakeEgraph {
    type EClassId = usize;
    type ENodeId = usize;
    fn print_node(&mut self, node: &usize) -> String {
        format!("{node}")
    }
    fn cost(&self, node: &usize) -> usize {
        self.nodes[*node].1
    }
    fn expand_class(&mut self, class: &usize, nodes: &mut Vec<usize>) {
        nodes.extend_from_slice(&self.classes[*class])
    }
    fn get_children(&mut self, node: &usize, classes: &mut Vec<usize>) {
        classes.extend_from_slice(&self.nodes[*node].0)
    }
}

#[test]
fn extract_tiny_egraph() {
    let mut egraph = FakeEgraph {
        nodes: vec![(vec![], 1)],
        classes: vec![vec![0]],
    };

    let (result, _) = extract_zdd(&mut egraph, 0, None).expect("extraction should succeed");
    assert_eq!(result.total_cost, 1);
    assert_eq!(result.dag.node_count(), 1);
}

#[test]
fn extract_tiny_egraph_greedy() {
    let mut egraph = FakeEgraph {
        nodes: vec![(vec![], 1)],
        classes: vec![vec![0]],
    };

    let result = extract_greedy(&mut egraph, 0).expect("extraction should succeed");
    assert_eq!(result.total_cost, 1);
    assert_eq!(result.dag.node_count(), 1);
}

#[test]
fn extract_sharing() {
    let mut egraph = egraph_sharing();
    let (result, _) = extract_zdd(&mut egraph, 0, None).expect("extraction should succeed");
    assert_eq!(result.dag.node_count(), 3);
    assert_eq!(result.total_cost, 6);
    const EXPECTED: &str = r#"digraph {
    0 [ label = "0" ]
    1 [ label = "3" ]
    2 [ label = "1" ]
    0 -> 1 [ label = "()" ]
    2 -> 1 [ label = "()" ]
    0 -> 2 [ label = "()" ]
}
"#;
    assert_eq!(format!("{:?}", Dot::new(&result.dag)), EXPECTED);
}

#[test]
fn extract_sharing_low_limit() {
    // If we lower the node limit to only contain a single element at a time, we
    // get a DAG isomorphic to the one returned by greedy.
    let mut egraph = egraph_sharing();
    let (result, _) = extract_zdd(&mut egraph, 0, Some(2)).expect("extraction should succeed");
    assert_eq!(result.dag.node_count(), 4);
    assert_eq!(result.total_cost, 7);
    const EXPECTED: &str = r#"digraph {
    0 [ label = "0" ]
    1 [ label = "3" ]
    2 [ label = "2" ]
    3 [ label = "4" ]
    0 -> 1 [ label = "()" ]
    2 -> 3 [ label = "()" ]
    0 -> 2 [ label = "()" ]
}
"#;
    assert_eq!(format!("{:?}", Dot::new(&result.dag)), EXPECTED);
}

#[test]
fn extract_sharing_greedy() {
    let mut egraph = egraph_sharing();
    let result = extract_greedy(&mut egraph, 0).expect("extraction should succeed");
    assert_eq!(result.dag.node_count(), 4);
    assert_eq!(result.total_cost, 7);
    const EXPECTED: &str = r#"digraph {
    0 [ label = "0" ]
    1 [ label = "3" ]
    3 [ label = "2" ]
    4 [ label = "4" ]
    0 -> 1 [ label = "()" ]
    3 -> 4 [ label = "()" ]
    0 -> 3 [ label = "()" ]
}
"#;
    assert_eq!(format!("{:?}", Dot::new(&result.dag)), EXPECTED);
}

fn egraph_sharing() -> FakeEgraph {
    FakeEgraph {
        classes: vec![
            // R
            vec![0],
            // A
            vec![1, 2],
            // B
            vec![3],
            // C
            vec![4],
        ],
        nodes: vec![
            // a
            (vec![2, 1], 2),
            // b
            (vec![2], 2),
            // c
            (vec![3], 2),
            // d
            (vec![], 2),
            // e
            (vec![], 1),
        ],
    }
}

#[test]
fn print_egraph_example() {
    let mut egraph = egraph_example();

    eprintln!(
        "{}",
        render_zdd(&mut egraph, 0, |n| {
            match *n {
                0 => "root",
                1 => "a",
                2 => "b",
                3 => "c",
                4 => "d",
                5 => "e",
                6 => "f",
                7 => "g",
                8 => "h",
                _ => "UNKNOWN",
            }
            .into()
        })
    );
    let mut report = Report::default();
    choose_nodes(&mut egraph, 0, Some(&mut report), None);
    eprintln!("{report}");
}

fn egraph_example() -> FakeEgraph {
    let _c_root = 0;
    let c_w = 1;
    let c_x = 2;
    let c_y = 3;
    let c_z = 4;

    let n_root = 0;
    let n_a = 1;
    let n_b = 2;
    let n_c = 3;
    let n_d = 4;
    let n_e = 5;
    let n_f = 6;

    FakeEgraph {
        nodes: vec![
            // n_root
            (vec![c_w, c_x], 1),
            // n_a
            (vec![c_y, c_z], 1),
            // n_b
            (vec![c_y], 1),
            // n_c
            (vec![c_y, c_z], 1),
            // n_d
            (vec![c_z], 1),
            // n_e
            (vec![], 1),
            // n_f
            (vec![], 1),
        ],
        classes: vec![
            // c_root
            vec![n_root],
            // c_w
            vec![n_a, n_b],
            // c_x
            vec![n_c, n_d],
            // c_y
            vec![n_e],
            // c_z
            vec![n_f],
        ],
    }
}

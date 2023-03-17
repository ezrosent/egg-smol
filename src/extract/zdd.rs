//! Optimal extraction using ZDDs

// TODO:
// 1. EClassId = Id, ENodeId = (Symbol, usize /* table offset */)
// 2. Build some indexes:
//    ENodeId => EClassId
// Once we extract the min-cost set of enodes we can then invert the index:
//    EClassId => ENodeId (best)
// By just mapping the first index across the set.
// 3. With that, we can recursively build up an Expr as in the greedy case. (and
// we'll figure out what's going on with the base cases soon)
use symbol_table::GlobalSymbol;

use crate::{ast::Expr, util::HashMap, EGraph, Value};

use super::Cost;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum ENodeId {
    Prim(Value),
    EqAble { func: GlobalSymbol, offset: u32 },
}

struct Extractor<'a> {
    egraph: &'a EGraph,
    // Map from sort to names of functions with output for that sort
    constructors: HashMap<GlobalSymbol, Vec<GlobalSymbol>>,
    node_ids: HashMap<ENodeId, Value>,
    min_costs: HashMap<Value, ENodeId>,
}

const ZDD_NODE_LIMIT: Option<usize> = Some(16 << 10);

impl EGraph {
    /// Extract the minimum-cost expression associated with the value.
    ///
    /// This method uses ZDDs to enumerate the entire space of choices for each
    /// id reachable from the given value.
    pub fn optimal_expr(&self, v: Value) -> Option<(Cost, Expr)> {
        let mut extractor = Extractor::new(self);
        let (nodes, cost) = zdds::choose_nodes(&mut extractor, v, None, ZDD_NODE_LIMIT)?;
        extractor.process_best(&nodes);
        Some((cost, extractor.extract_best(&v)))
    }

    /// Compute the lowest cost extraction for the value without reconstructing
    /// the whole expression.
    pub fn optimal_cost(&self, v: Value) -> Option<(Cost, zdds::Report)> {
        let mut extractor = Extractor::new(self);
        let mut report = zdds::Report::default();
        let (_, cost) = zdds::choose_nodes(&mut extractor, v, Some(&mut report), ZDD_NODE_LIMIT)?;
        Some((cost, report))
    }
}

impl<'a> zdds::Egraph for Extractor<'a> {
    type EClassId = Value;
    type ENodeId = ENodeId;
    fn cost(&self, node: &ENodeId) -> usize {
        match node {
            ENodeId::Prim(_) => 0,
            ENodeId::EqAble { func, .. } => {
                let func = &self.egraph.functions[func];
                func.decl.cost.unwrap_or(1)
            }
        }
    }
    fn print_node(&mut self, node: &ENodeId) -> String {
        match node {
            ENodeId::Prim(v) => {
                format!("prim({v:?})")
            }
            ENodeId::EqAble { func, offset } => {
                let (inputs, output) = self.get_tuple(*func, *offset);
                format!("{func}({inputs:?} => {output:?})")
            }
        }
    }
    fn expand_class(&mut self, class: &Value, nodes: &mut Vec<ENodeId>) {
        let sort = self.egraph.get_sort(class).expect("sort must be bound");
        if sort.is_eq_sort() {
            for func_name in &self.constructors[&class.tag] {
                let func = &self.egraph.functions[func_name];
                // TODO: confirm the indexes are up to date.
                let index = func.indexes.last().unwrap();
                for node in index.get(class).into_iter().flat_map(|x| {
                    x.iter().copied().filter_map(|offset| {
                        func.nodes.get_index(offset as usize)?;
                        Some(ENodeId::EqAble {
                            func: *func_name,
                            offset,
                        })
                    })
                }) {
                    self.node_ids.insert(node, *class);
                    nodes.push(node)
                }
            }
        } else {
            let node = ENodeId::Prim(*class);
            self.node_ids.insert(node, *class);
            nodes.push(node);
        }
    }
    fn get_children(&mut self, node: &ENodeId, classes: &mut Vec<Value>) {
        match node {
            ENodeId::EqAble { func, offset } => {
                let (inputs, _) = self.get_tuple(*func, *offset);
                classes.extend(inputs.iter().copied());
            }
            ENodeId::Prim(_) => {}
        }
    }
}

impl<'a> Extractor<'a> {
    fn new(egraph: &EGraph) -> Extractor {
        let mut constructors = HashMap::<GlobalSymbol, Vec<GlobalSymbol>>::default();
        for (func_name, func) in &egraph.functions {
            constructors
                .entry(func.schema.output.name())
                .or_default()
                .push(*func_name);
        }
        Extractor {
            egraph,
            constructors,
            node_ids: Default::default(),
            min_costs: Default::default(),
        }
    }

    fn get_tuple(&self, func: GlobalSymbol, offset: u32) -> (&[Value], Value) {
        let (inputs, output) = self.egraph.functions[&func]
            .nodes
            .get_index(offset as usize)
            .expect("offsets generated by extractor should be valid");
        (inputs, output.value)
    }

    fn process_best(&mut self, nodes: &[ENodeId]) {
        for node in nodes {
            let class = self.node_ids[node];
            let _prev = self.min_costs.insert(class, *node);
            debug_assert!(_prev.is_none(), "min-cost enodes should be unique!");
        }
    }

    fn extract_best(&self, class: &Value) -> Expr {
        let node = &self.min_costs[class];
        match node {
            ENodeId::Prim(v) => self.egraph.get_sort(v).unwrap().make_expr(*v),
            ENodeId::EqAble { func, offset } => {
                let (inputs, _) = self.egraph.functions[func]
                    .nodes
                    .get_index(*offset as usize)
                    .unwrap();
                Expr::call(*func, inputs.iter().map(|v| self.extract_best(v)))
            }
        }
    }
}

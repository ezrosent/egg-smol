use std::mem;

use actions::{run_instrs, Rule, RuleBuilder, RuleId};
use common::{DenseIdMap, NumericId};
use free_join::{
    execute::{Runner, TimestampRange},
    plan::PlanStrategy,
    QueryBuilder, Variable,
};
use function::{index_cache::IndexCache, table::Timestamp, Function, Value};
use pool::{Pool, PoolSet};
use primitives::Primitives;
use schema::{ColumnTy, FunctionId, Schema};
use uf::UpdateTrackingUnionFind;

pub(crate) mod actions;
pub(crate) mod common;
pub(crate) mod free_join;
pub(crate) mod function;
pub(crate) mod pool;
pub(crate) mod primitives;
pub(crate) mod schema;
pub(crate) mod uf;

pub type Result<T> = std::result::Result<T, anyhow::Error>;

pub struct Db<'pool, 'outer> {
    functions: DenseIdMap<FunctionId, Function<'pool>>,
    prims: Primitives,
    cur_ts: Timestamp,
    uf: UpdateTrackingUnionFind<Value>,
    rules: DenseIdMap<RuleId, Rule>,
    index_cache: IndexCache<'pool>,
    pool_set: &'outer PoolSet<'pool>,
}

impl<'pool, 'outer> Db<'pool, 'outer> {
    pub fn new(pool_set: &'outer PoolSet<'pool>) -> Db<'pool, 'outer> {
        Db {
            functions: DenseIdMap::new(),
            prims: Default::default(),
            rules: DenseIdMap::new(),
            uf: Default::default(),
            index_cache: IndexCache::new(pool_set),
            cur_ts: Timestamp::new(0),
            pool_set,
        }
    }
    pub fn declare_function(&mut self, schema: Schema) -> FunctionId {
        self.functions.push(Function::new(schema, self.pool_set))
    }

    pub fn query_builder<'a>(&'a mut self) -> QueryBuilder<'a, 'pool, 'outer> {
        QueryBuilder::new(self)
    }

    pub fn standalone_rule<'a>(&'a mut self) -> RuleBuilder<'a, 'pool, 'outer> {
        RuleBuilder::new(None, self)
    }

    /// Run the specified rules using the default planning algorithm.
    pub fn run_rules(&mut self, to_run: &[RuleId]) {
        self.run_rules_with(to_run, PlanStrategy::default(), |_, _| {})
    }

    /// Get the total number of entries in the database.
    pub fn db_size(&self) -> usize {
        self.funcs().iter().map(|(_, f)| f.table().len()).sum()
    }

    /// Run the specified rules with the given strategy, along with a callback
    /// run against each of the variables bound by the rules.
    pub fn run_rules_with(
        &mut self,
        to_run: &[RuleId],
        strategy: PlanStrategy,
        mut f: impl FnMut(RuleId, &DenseIdMap<Variable, Value>),
    ) {
        self.inc_timestamp();
        let bindings_pool = Pool::<DenseIdMap<Variable, Value>>::default();
        let mut bindings_vec = Vec::new();
        let mut rules = mem::take(&mut self.rules);
        for rule_id in to_run.iter().copied() {
            let rule = &mut rules[rule_id];
            if let Some(query) = &rule.query {
                let mut runner = Runner::new(
                    TimestampRange {
                        low: rule.next_run,
                        high: self.cur_ts,
                    },
                    strategy,
                    &self.functions,
                    &mut self.index_cache,
                    self.pool_set,
                );
                runner.run(query, |bindings| {
                    let mut copy = bindings_pool.get_default();
                    copy.copy_from(bindings);
                    bindings_vec.push(copy);
                });
                for mut bindings in bindings_vec.drain(..) {
                    run_instrs(&mut bindings, self, rule.instrs(), |bindings| {
                        f(rule_id, bindings)
                    })
                }
                rule.next_run = self.cur_ts;
            } else {
                let mut bindings = bindings_pool.get_default();
                run_instrs(&mut bindings, self, rule.instrs(), |bindings| {
                    f(rule_id, bindings)
                })
            }
        }
        self.rules = rules;
    }

    /// Whether the database changed in the last call to `run_rules` or since
    /// the last call to `rebuild_all`.
    ///
    /// This functions is useful for running until the database reaches a fixed
    /// point. It requires O(n) time where n is the number of functions in the
    /// database.
    pub fn changed(&self) -> bool {
        if self.uf.has_pending_changes() {
            return true;
        }
        if self.cur_ts == Timestamp::new(0) {
            return false;
        }
        for (_, func) in self.functions.iter() {
            if func.table().last_changed() >= self.cur_ts {
                return true;
            }
        }
        false
    }

    pub fn rebuild_all(&mut self) {
        self.uf.advance();
        while !self.uf.recent_reparents().is_empty() {
            for (_, func) in self.functions.iter_mut() {
                match *func.schema().ret() {
                    ColumnTy::Id => {
                        func.table_mut()
                            .rebuild(self.cur_ts, &mut self.uf, |uf, l, r| uf.union(l, r).0);
                    }
                    ColumnTy::Primitive(p) => {
                        func.table_mut().rebuild(self.cur_ts, &mut self.uf, |_, l, r| {
                            if l == r {
                                return l;
                            }
                            panic!("attempt to merge primitives ({p:?}): l={l:?} r={r:?}; that's currently unsupported")
                        });
                    }
                }
            }
            self.uf.advance();
        }
    }

    /// Get the canonical version of the value.
    ///
    /// # Panics
    /// This method may (but is not guaranteed to) panic if `val` is not an Id
    /// value.
    pub fn canonicalize(&mut self, val: Value) -> Value {
        self.uf.find(val)
    }

    pub(crate) fn get(&self, func: FunctionId, args: &[Value]) -> Option<Value> {
        self.functions[func].get(args)
    }

    pub(crate) fn get_with_default(&mut self, func: FunctionId, args: &[Value]) -> Value {
        let func = &mut self.functions[func];
        match func.schema().ret() {
            ColumnTy::Id => func.get_with_default(args, self.cur_ts, &mut self.uf, |uf| uf.fresh()),
            ColumnTy::Primitive(_) => {
                func.get_with_default(args, self.cur_ts, &mut self.uf, |_| {
                    panic!("primitive default are not supported")
                })
            }
        }
    }

    /// Increment the timestamp applied to new writes to the database.
    pub(crate) fn inc_timestamp(&mut self) {
        self.cur_ts = Timestamp::from_usize(self.cur_ts.index() + 1);
    }

    /// Add a rule to the database.
    pub(crate) fn add_rule(&mut self, rule: Rule) -> RuleId {
        self.rules.push(rule)
    }

    /// Insert `args` mapped to `ret` in the given function `func`.
    pub(crate) fn insert(&mut self, func: FunctionId, args: &[Value], ret: Value) {
        let func = &mut self.functions[func];
        func.insert(args, ret, self.cur_ts, &mut self.uf);
    }

    /// Remove the entry for `args` in the given function `func` if it is there.
    pub(crate) fn remove(&mut self, func: FunctionId, args: &[Value]) {
        let func = &mut self.functions[func];
        func.table_mut().remove(args);
    }

    /// Get a mutable reference to the underlying union-find data-structure.
    pub(crate) fn uf(&mut self) -> &mut UpdateTrackingUnionFind<Value> {
        &mut self.uf
    }

    pub(crate) fn pool_set(&self) -> &'outer PoolSet<'pool> {
        self.pool_set
    }

    /// Returns a reference to the underlying function array; used for unit tests.
    pub(crate) fn funcs(&self) -> &DenseIdMap<FunctionId, Function<'pool>> {
        &self.functions
    }

    #[cfg(test)]
    #[allow(unused)]
    /// This is just used for debugging during a test.
    pub(crate) fn dump_table(&self, func: FunctionId) {
        self.functions[func].table().iter().for_each(|(args, ret)| {
            eprintln!("{args:?} => {ret:?}");
        });
    }

    /// Returns a mutable reference to the set of primitives recognized by the database.
    pub fn prims_mut(&mut self) -> &mut Primitives {
        &mut self.prims
    }

    /// Returns a reference to the set of primitives recognized by the database.
    pub(crate) fn prims(&self) -> &Primitives {
        &self.prims
    }
}

#[cfg(test)]
mod tests;

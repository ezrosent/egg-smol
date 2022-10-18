pub mod ast;
mod extract;
mod gj;
pub mod sort;
mod typecheck;
mod unionfind;
mod util;
mod value;

use hashbrown::hash_map::Entry;
use indexmap::map::Entry as IEntry;
use instant::{Duration, Instant};
use smallvec::SmallVec;
use sort::*;
use thiserror::Error;

use ast::*;

use std::borrow::Borrow;
use std::cell::Cell;
use std::fmt::Write;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Read;
use std::iter;
use std::mem;
use std::ops::{Deref, Range};
use std::path::PathBuf;
use std::{fmt::Debug, sync::Arc};
use typecheck::{AtomTerm, Bindings};

type ArcSort = Arc<dyn Sort>;

pub use value::*;

use gj::*;

use unionfind::*;
use util::*;

use crate::typecheck::TypeError;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct FunctionKey {
    inputs: Vec<Value>,
    /// We want to keep functions sorted by timestamp, but rebuilding perturbs
    /// the order by removing an old copy of a node and inserting a new one.
    /// Re-sorting after this removal requires O(n) work.
    ///
    /// Instead, we mark rebuilt entries as 'stale' and ignore them during
    /// lookups. If the number of tombstones gets too high we can pay an O(n)
    /// cost to remove them all at once. Non-stale tuples have this value set to
    /// 0.
    stale: usize,
}

/// We want to be able to look up a FunctionKey in a map purely based on a slice
/// of values, but the hash function for &[Value] does not line up with the
/// synthesized function for FunctionKey. KeyRef adds "stale: false" to the hash
/// function for the value slice, making it suitable for map lookups.
#[derive(Eq, Debug)]
#[repr(transparent)]
struct KeyRef(pub(crate) [Value]);

impl KeyRef {
    fn from_slice(vals: &[Value]) -> &KeyRef {
        // Safety: KeyRef is #[repr(transparent)]
        unsafe { std::mem::transmute::<&[Value], &KeyRef>(vals) }
    }
}

impl Hash for KeyRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        0usize.hash(state);
    }
}

impl PartialEq for KeyRef {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Borrow<KeyRef> for FunctionKey {
    fn borrow(&self) -> &KeyRef {
        KeyRef::from_slice(self.vals())
    }
}

impl FunctionKey {
    pub(crate) fn vals(&self) -> &[Value] {
        self.inputs.as_slice()
    }
    pub(crate) fn vals_mut(&mut self) -> &mut [Value] {
        self.inputs.as_mut_slice()
    }

    pub(crate) fn from_vec(inputs: Vec<Value>) -> FunctionKey {
        FunctionKey { inputs, stale: 0 }
    }
}

/// A key used to identify a trie built on a particular function.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct TrieSpec {
    columns: SmallVec<[u32; 4]>,
    constraints: SmallVec<[Constraint; 1]>,
}

impl TrieSpec {
    fn new(
        columns: impl Iterator<Item = u32>,
        constraints: impl Iterator<Item = Constraint>,
    ) -> TrieSpec {
        let columns = columns.collect();
        let mut constraints: SmallVec<[Constraint; 1]> = constraints.collect();
        constraints.sort_unstable();
        constraints.dedup();
        TrieSpec {
            columns,
            constraints,
        }
    }
}

#[derive(Clone)]
pub struct Function {
    decl: FunctionDecl,
    schema: ResolvedSchema,
    nodes: IndexMap<FunctionKey, TupleOutput>,
    stale_entries: usize,
    updates: usize,
    counter: Cell<usize>,
}

#[derive(Debug, Clone)]
struct TupleOutput {
    value: Value,
    timestamp: u32,
}

#[derive(Clone, Debug)]
struct ResolvedSchema {
    input: Vec<ArcSort>,
    output: ArcSort,
}

pub(crate) struct FunctionEntry<'a> {
    /// The index into the table where this entry is stored.
    index: usize,
    /// The arguments to the function in question.
    inputs: &'a [Value],
    /// The return value corresponding to the arguments to this function.
    out: Value,
}

impl Function {
    pub fn insert(&mut self, inputs: Vec<Value>, value: Value, timestamp: u32) -> Option<Value> {
        self.insert_raw(FunctionKey::from_vec(inputs), |_, _| value, timestamp)
    }

    fn insert_raw(
        &mut self,
        inputs: FunctionKey,
        mut update: impl FnMut(Option<(Value, u32)>, &mut u32) -> Value,
        mut timestamp: u32,
    ) -> Option<Value> {
        enum Action {
            Done(Option<Value>),
            Repair {
                index: usize,
                old_ts: u32,
                saved: Value,
            },
        }
        let action = match self.nodes.entry(inputs) {
            IEntry::Occupied(mut entry) => {
                let old = entry.get_mut();
                let to_insert = update(Some((old.value, old.timestamp)), &mut timestamp);
                if old.value == to_insert {
                    Action::Done(Some(to_insert))
                } else {
                    let old_ts = old.timestamp;
                    let saved = old.value;
                    old.value = to_insert;
                    old.timestamp = timestamp.max(old.timestamp);
                    self.updates += 1;
                    debug_assert_ne!(saved, to_insert);
                    if old_ts == timestamp {
                        Action::Done(Some(saved))
                    } else {
                        Action::Repair {
                            index: entry.index(),
                            old_ts,
                            saved,
                        }
                    }
                }
            }
            IEntry::Vacant(entry) => {
                let value = update(None, &mut timestamp);
                entry.insert(TupleOutput { value, timestamp });
                self.updates += 1;
                Action::Done(None)
            }
        };
        let res = match action {
            Action::Done(v) => v,
            Action::Repair {
                index,
                old_ts,
                saved,
            } => {
                // add 1 to ensure nonzero
                let stale = self.nodes.len() + 1;
                let new_index = self.nodes.len();
                let mut _unused = old_ts;
                let tombstone = self.tombstone();
                let was = self.nodes.insert(
                    tombstone,
                    TupleOutput {
                        value: update(None, &mut _unused),
                        timestamp: old_ts,
                    },
                );
                assert!(was.is_none());
                self.nodes.swap_indices(index, new_index);
                self.stale_entries += 1;
                Some(saved)
            }
        };
        self.maybe_rehash();
        res
    }

    fn tombstone(&self) -> FunctionKey {
        let res = FunctionKey {
            inputs: Default::default(),
            stale: self.counter.get(),
        };
        self.counter.set(self.counter.get() + 1);
        res
    }

    fn maybe_rehash(&mut self) {
        if self.nodes.len() > 8 && self.stale_entries >= (self.nodes.len() / 2) {
            self.nodes.retain(|k, _| k.stale == 0);
            self.stale_entries = 0;
        }
    }

    pub fn rebuild(&mut self, uf: &mut UnionFind, timestamp: u32) -> usize {
        if self.schema.input.iter().all(|s| !s.is_eq_sort()) && !self.schema.output.is_eq_sort() {
            return mem::take(&mut self.updates);
        }
        let updates = self.updates;

        // FIXME this doesn't compute updates properly
        let n_unions = uf.n_unions();
        let mut scratch = Vec::new();
        for i in 0..self.nodes.len() {
            let (inputs, output) = self.nodes.get_index(i).unwrap();
            if inputs.stale != 0 {
                continue;
            }

            scratch.clear();
            scratch.extend(inputs.inputs.iter().copied());
            let mut ret = output.value;
            let mut changed = false;
            for (v, ty) in scratch
                .iter_mut()
                .zip(&self.schema.input)
                .chain(iter::once((&mut ret, &self.schema.output)))
            {
                if ty.is_eq_sort() {
                    let new = uf.find_mut_value(*v);
                    changed |= &new != v;
                    *v = new;
                }
            }
            if !changed {
                continue;
            }
            // The canonical representation changed. We need to reinsert and perhaps do a merge.
            // 1. swap in a tombstone
            let tombstone = self.tombstone();
            assert!(self.nodes.insert(tombstone, output.clone()).is_none());
            self.stale_entries += 1;
            let (prev, _) = self.nodes.swap_remove_index(i).unwrap();
            // 2. Insert the canonicalized data
            let new_key = FunctionKey::from_vec(scratch);
            struct RemoveAndInsert {
                index: usize,
                inputs: FunctionKey,
                output: Value,
                prev_ts: u32,
            }
            let action = match self.nodes.entry(new_key) {
                IEntry::Occupied(mut o) => {
                    // 3a. The canonicalized tuple is already in the map. Update
                    // its timestamp and merge the outputs if necessary.
                    if self.schema.output.is_eq_sort() {
                        let next_val = uf.union_values(o.get().value, ret);
                        let prev_ts = o.get().timestamp;
                        if prev_ts == timestamp {
                            // Timestamps match, we can update in place
                            o.get_mut().value = next_val;
                            None
                        } else {
                            Some(RemoveAndInsert {
                                index: o.index(),
                                inputs: o.key().clone(),
                                output: next_val,
                                prev_ts,
                            })
                        }
                    } else {
                        // Do nothing
                        // TODO: apply merge functions
                        None
                    }
                }
                IEntry::Vacant(v) => {
                    // 3b. Insert the new node at the specified timestamp
                    v.insert(TupleOutput {
                        value: ret,
                        timestamp,
                    });
                    None
                }
            };
            if let Some(RemoveAndInsert {
                index,
                inputs,
                output,
                prev_ts,
            }) = action
            {
                // Tombstone the entry that we will merge in
                let tombstone = self.tombstone();
                assert!(self
                    .nodes
                    .insert(
                        tombstone,
                        TupleOutput {
                            value: output,
                            timestamp: prev_ts
                        }
                    )
                    .is_none());
                self.nodes.swap_remove_index(index).unwrap();
                self.stale_entries += 1;
                // Add the newly-merged tuple to the end of the map
                assert!(self
                    .nodes
                    .insert(
                        inputs,
                        TupleOutput {
                            value: output,
                            timestamp
                        }
                    )
                    .is_none());
            }
            scratch = prev.inputs;
        }
        self.maybe_rehash();
        self.updates = 0;
        uf.n_unions() - n_unions + updates
    }

    pub(crate) fn get_size(&self, range: &Range<u32>) -> usize {
        self.nodes
            .values()
            .filter(|out| range.contains(&out.timestamp))
            .count()
        // if range.start == 0 {
        //     if range.end == u32::MAX {
        //         self.nodes.len()
        //     } else {
        //         // TODO binary search or something
        //         self.nodes
        //             .values()
        //             .filter(|out| out.timestamp < range.end)
        //             .count()
        //     }
        // } else {
        //     assert_eq!(range.end, u32::MAX);
        //     self.nodes
        //         .values()
        //         .filter(|out| out.timestamp >= range.end)
        //         .count()
        // }
    }

    /// Iterate over the nodes in the given timestamp range for the function. Returns the
    pub(crate) fn iter_timestamp_range(
        &self,
        range: Range<u32>,
    ) -> impl Iterator<Item = FunctionEntry> {
        self.nodes
            .iter()
            .enumerate()
            .filter_map(move |(i, (args, out))| {
                if args.stale != 0 || !range.contains(&out.timestamp) {
                    return None;
                }
                Some(FunctionEntry {
                    index: i,
                    inputs: args.vals(),
                    out: out.value,
                })
            })
    }

    /// Iterate over the subset of entries in the table at the given indexes
    /// that fall in the given timestamp range.
    pub(crate) fn project_from_timestamp_range<'a>(
        &'a self,
        ixs: &'a [u32],
        timestamp_range: Range<u32>,
    ) -> impl Iterator<Item = FunctionEntry<'a>> {
        ixs.iter().filter_map(move |x| {
            let index = *x as usize;
            let (args, out) = self
                .nodes
                .get_index(index)
                .expect("index should be in range");
            if args.stale != 0 || !timestamp_range.contains(&out.timestamp) {
                return None;
            }
            Some(FunctionEntry {
                index,
                inputs: args.vals(),
                out: out.value,
            })
        })
    }
}

pub type Subst = IndexMap<Symbol, Value>;

pub trait PrimitiveLike {
    fn name(&self) -> Symbol;
    fn accept(&self, types: &[&dyn Sort]) -> Option<ArcSort>;
    fn apply(&self, values: &[Value]) -> Option<Value>;
}

#[derive(Clone)]
pub struct Primitive(Arc<dyn PrimitiveLike>);

impl Deref for Primitive {
    type Target = dyn PrimitiveLike;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl Hash for Primitive {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

impl Eq for Primitive {}
impl PartialEq for Primitive {
    fn eq(&self, other: &Self) -> bool {
        // this is a bit of a hack, but clippy says we don't want to compare the
        // vtables, just the data pointers
        std::ptr::eq(
            Arc::as_ptr(&self.0) as *const u8,
            Arc::as_ptr(&other.0) as *const u8,
        )
    }
}

impl Debug for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Prim({})", self.0.name())
    }
}

impl<T: PrimitiveLike + 'static> From<T> for Primitive {
    fn from(p: T) -> Self {
        Self(Arc::new(p))
    }
}

pub struct SimplePrimitive {
    name: Symbol,
    input: Vec<ArcSort>,
    output: ArcSort,
    f: fn(&[Value]) -> Option<Value>,
}

impl PrimitiveLike for SimplePrimitive {
    fn name(&self) -> Symbol {
        self.name
    }
    fn accept(&self, types: &[&dyn Sort]) -> Option<ArcSort> {
        if self.input.len() != types.len() {
            return None;
        }
        // TODO can we use a better notion of equality than just names?
        self.input
            .iter()
            .zip(types)
            .all(|(a, b)| a.name() == b.name())
            .then(|| self.output.clone())
    }
    fn apply(&self, values: &[Value]) -> Option<Value> {
        (self.f)(values)
    }
}

#[derive(Clone)]
pub struct EGraph {
    egraphs: Vec<Self>,
    unionfind: UnionFind,
    presorts: HashMap<Symbol, PreSort>,
    sorts: HashMap<Symbol, Arc<dyn Sort>>,
    primitives: HashMap<Symbol, Vec<Primitive>>,
    functions: HashMap<Symbol, Function>,
    rules: HashMap<Symbol, Rule>,
    saturated: bool,
    timestamp: u32,
    pub match_limit: usize,
    pub fact_directory: Option<PathBuf>,
}

#[derive(Clone, Debug)]
struct Rule {
    query: CompiledQuery,
    bindings: Bindings,
    head: Vec<Action>,
    matches: usize,
    times_banned: usize,
    banned_until: usize,
    todo_timestamp: u32,
    search_time: Duration,
    apply_time: Duration,
}

impl Default for EGraph {
    fn default() -> Self {
        let mut egraph = Self {
            egraphs: vec![],
            unionfind: Default::default(),
            sorts: Default::default(),
            functions: Default::default(),
            rules: Default::default(),
            primitives: Default::default(),
            presorts: Default::default(),
            match_limit: 10_000_000,
            timestamp: 0,
            saturated: false,
            fact_directory: None,
        };
        egraph.add_sort(UnitSort::new("Unit".into()));
        egraph.add_sort(StringSort::new("String".into()));
        egraph.add_sort(I64Sort::new("i64".into()));
        egraph.add_sort(RationalSort::new("Rational".into()));
        egraph.presorts.insert("Map".into(), MapSort::make_sort);
        egraph
    }
}

#[derive(Debug, Error)]
#[error("Not found: {0}")]
pub struct NotFoundError(Expr);

impl EGraph {
    pub fn add_sort<S: Sort + 'static>(&mut self, sort: S) {
        self.add_arcsort(Arc::new(sort));
    }

    pub fn push(&mut self) {
        self.egraphs.push(self.clone());
    }

    pub fn pop(&mut self) -> Result<(), Error> {
        match self.egraphs.pop() {
            Some(e) => {
                *self = e;
                Ok(())
            }
            None => Err(Error::Pop),
        }
    }

    pub fn add_arcsort(&mut self, sort: ArcSort) {
        match self.sorts.entry(sort.name()) {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => {
                e.insert(sort.clone());
                sort.register_primitives(self);
            }
        };
    }

    fn get_sort<S: Sort + Send + Sync>(&self) -> Arc<S> {
        for sort in self.sorts.values() {
            let sort = sort.clone().as_arc_any();
            if let Ok(sort) = Arc::downcast(sort) {
                return sort;
            }
        }
        // TODO handle if multiple match?
        // could handle by type id??
        panic!("Failed to lookup sort: {}", std::any::type_name::<S>());
    }

    fn add_primitive(&mut self, prim: impl Into<Primitive>) {
        let prim = prim.into();
        self.primitives.entry(prim.name()).or_default().push(prim);
    }

    pub fn union(&mut self, id1: Id, id2: Id) -> Id {
        self.unionfind.union(id1, id2)
    }

    #[track_caller]
    fn debug_assert_invariants(&self) {
        #[cfg(debug_assertions)]
        for (name, function) in self.functions.iter() {
            let ts: Vec<_> = function.nodes.values().map(|x| x.timestamp).collect();
            assert!(
                ts.windows(2).all(|x| x[0] <= x[1]),
                "{:?}\n{:?}",
                function.nodes,
                ts
            );
            for (inputs, output) in function.nodes.iter() {
                if inputs.stale != 0 {
                    continue;
                }

                for input in inputs.vals() {
                    assert_eq!(
                        input,
                        &self.bad_find_value(*input),
                        "{name}({inputs:?}) = {output:?}\n{:?}",
                        function.schema,
                    )
                }
                assert_eq!(
                    output.value,
                    self.bad_find_value(output.value),
                    "{name}({inputs:?}) = {output:?}\n{:?}",
                    function.schema,
                )
            }
        }
    }

    pub fn union_exprs(&mut self, ctx: &Subst, exprs: &[Expr]) -> Result<Value, NotFoundError> {
        let mut exprs = exprs.iter();
        let e = exprs.next().expect("shouldn't be empty");
        let mut val = self.eval_expr(ctx, e)?;
        for e2 in exprs {
            let val2 = self.eval_expr(ctx, e2)?;
            val = self.unionfind.union_values(val, val2);
        }
        Ok(val)
    }

    pub fn eval_actions(
        &mut self,
        mut ctx: Option<Subst>,
        actions: &[Action],
    ) -> Result<(), Error> {
        let default = Subst::default();
        for action in actions {
            match action {
                Action::Panic(msg) => {
                    panic!("panic {} {:?}", msg, ctx.as_ref().unwrap_or(&default))
                }
                Action::Expr(e) => {
                    self.eval_expr(ctx.as_ref().unwrap_or(&default), e)?;
                }
                Action::Define(x, e) => {
                    if let Some(ctx) = ctx.as_mut() {
                        let value = self.eval_expr(ctx, e)?;
                        ctx.insert(*x, value);
                    } else {
                        unreachable!("Global define should be handled elsewhere");
                        // let value = self.eval_expr(&default, e)?;
                        // self.globals.insert(*x, value);
                    }
                }
                Action::Set(f, args, e) => {
                    let ctx = ctx.as_ref().unwrap_or(&default);
                    let values = args
                        .iter()
                        .map(|a| self.eval_expr(ctx, a))
                        .collect::<Result<Vec<_>, _>>()?;
                    let value = self.eval_expr(ctx, e)?;
                    let function = self
                        .functions
                        .get_mut(f)
                        .ok_or_else(|| NotFoundError(e.clone()))?;
                    let old_value = function.insert(values.clone(), value, self.timestamp);

                    // if the value does not exist or the two values differ
                    if old_value.is_none() || old_value != Some(value) {
                        self.saturated = false;
                    }

                    // TODO neaten saturation logic

                    if let Some(old_value) = old_value {
                        if value != old_value {
                            let out = &function.schema.output;
                            match function.decl.merge.as_ref() {
                                None if out.name().as_str() == "Unit" => (),
                                None if out.is_eq_sort() => {
                                    self.unionfind.union_values(old_value, value);
                                }
                                Some(expr) => {
                                    let mut ctx = Subst::default();
                                    ctx.insert("old".into(), old_value);
                                    ctx.insert("new".into(), value);
                                    let expr = expr.clone(); // break the borrow of `function`
                                    let new_value = self.eval_expr(&ctx, &expr)?;
                                    self.functions.get_mut(f).unwrap().insert(
                                        values,
                                        new_value,
                                        self.timestamp,
                                    );
                                }
                                _ => panic!("invalid merge for {}", function.decl.name),
                            }
                        }
                    }
                }
                Action::Union(a, b) => {
                    let ctx = ctx.as_ref().unwrap_or(&default);
                    let a = self.eval_expr(ctx, a)?;
                    let b = self.eval_expr(ctx, b)?;
                    if self.unionfind.find(Id::from(a.bits as usize))
                        != self.unionfind.find(Id::from(b.bits as usize))
                    {
                        self.saturated = false;
                    }
                    self.unionfind.union_values(a, b);
                }
                Action::Delete(sym, args) => {
                    let ctx = ctx.as_ref().unwrap_or(&default);
                    let values = args
                        .iter()
                        .map(|a| self.eval_expr(ctx, a))
                        .collect::<Result<Vec<_>, _>>()?;
                    let function = self
                        .functions
                        .get_mut(sym)
                        .ok_or(TypeError::Unbound(*sym))?;
                    if function
                        .nodes
                        .remove(&FunctionKey::from_vec(values))
                        .is_some()
                    {
                        self.saturated = false;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn check_with(&mut self, ctx: &Subst, fact: &Fact) -> Result<(), Error> {
        match fact {
            Fact::Eq(exprs) => {
                assert!(exprs.len() > 1);
                let values: Vec<Value> = exprs
                    .iter()
                    .map(|e| self.eval_expr(ctx, e).map(|v| self.bad_find_value(v)))
                    .collect::<Result<_, _>>()?;
                for v in &values[1..] {
                    if &values[0] != v {
                        println!("Check failed");
                        // the check failed, so print out some useful info
                        self.rebuild();
                        for value in &values {
                            if let Some((_tag, id)) = self.value_to_id(*value) {
                                let best = self.extract(*value).1;
                                println!("{}: {}", id, best);
                            }
                        }
                        return Err(Error::CheckError(values[0], *v));
                    }
                }
            }
            Fact::Fact(expr) => match expr {
                Expr::Lit(_) => panic!("can't assert a literal"),
                Expr::Var(_) => panic!("can't assert a var"),
                Expr::Call(sym, args) => {
                    let values: Vec<Value> = args
                        .iter()
                        .map(|e| self.eval_expr(ctx, e).map(|v| self.bad_find_value(v)))
                        .collect::<Result<_, _>>()?;
                    if let Some(f) = self.functions.get_mut(sym) {
                        // FIXME We don't have a unit value
                        assert_eq!(f.schema.output.name().as_str(), "Unit");
                        f.nodes
                            .get(&FunctionKey::from_vec(values))
                            .ok_or_else(|| NotFoundError(expr.clone()))?;
                    } else if self.primitives.contains_key(sym) {
                        // HACK
                        // we didn't typecheck so we don't know which prim to call
                        let val = self.eval_expr(ctx, expr)?;
                        assert_eq!(val, Value::unit());
                    } else {
                        return Err(Error::TypeError(TypeError::Unbound(*sym)));
                    }
                }
            },
        }
        Ok(())
    }

    pub fn find(&self, id: Id) -> Id {
        self.unionfind.find(id)
    }

    pub fn rebuild(&mut self) -> usize {
        let mut updates = 0;
        loop {
            let new = self.rebuild_one();
            log::debug!("{new} rebuilds?");
            updates += new;
            if new == 0 {
                break;
            }
        }
        self.debug_assert_invariants();
        updates
    }

    fn rebuild_one(&mut self) -> usize {
        let mut new_unions = 0;
        for function in self.functions.values_mut() {
            new_unions += function.rebuild(&mut self.unionfind, self.timestamp);
        }
        new_unions
    }

    pub fn declare_sort(&mut self, name: impl Into<Symbol>) -> Result<(), Error> {
        let name = name.into();
        match self.sorts.entry(name) {
            Entry::Occupied(_) => Err(Error::SortAlreadyBound(name)),
            Entry::Vacant(e) => {
                e.insert(Arc::new(EqSort { name }));
                Ok(())
            }
        }
    }

    pub fn declare_function(&mut self, decl: &FunctionDecl) -> Result<(), Error> {
        let mut input = Vec::with_capacity(decl.schema.input.len());
        for s in &decl.schema.input {
            input.push(match self.sorts.get(s) {
                Some(sort) => sort.clone(),
                None => return Err(Error::TypeError(TypeError::Unbound(*s))),
            })
        }

        let output = match self.sorts.get(&decl.schema.output) {
            Some(sort) => sort.clone(),
            None => return Err(Error::TypeError(TypeError::Unbound(decl.schema.output))),
        };

        let function = Function {
            decl: decl.clone(),
            schema: ResolvedSchema { input, output },
            nodes: Default::default(),
            stale_entries: 0,
            updates: 0,
            counter: Cell::new(1),
            // TODO figure out merge and default here
        };

        let old = self.functions.insert(decl.name, function);
        if old.is_some() {
            return Err(TypeError::FunctionAlreadyBound(decl.name).into());
        }

        Ok(())
    }

    pub fn declare_constructor(
        &mut self,
        variant: Variant,
        sort: impl Into<Symbol>,
    ) -> Result<(), Error> {
        let name = variant.name;
        let sort = sort.into();
        self.declare_function(&FunctionDecl {
            name,
            schema: Schema {
                input: variant.types,
                output: sort,
            },
            merge: None,
            default: None,
            cost: variant.cost,
        })?;
        // if let Some(ctors) = self.sorts.get_mut(&sort) {
        //     ctors.push(name);
        // }
        Ok(())
    }

    pub fn eval_lit(&self, lit: &Literal) -> Value {
        match lit {
            Literal::Int(i) => i.store(&*self.get_sort()).unwrap(),
            Literal::String(s) => s.store(&*self.get_sort()).unwrap(),
            Literal::Unit => ().store(&*self.get_sort()).unwrap(),
        }
    }

    // this must be &mut because it'll call "make_set",
    // but it'd be nice if that didn't have to happen
    pub fn eval_expr(&mut self, ctx: &Subst, expr: &Expr) -> Result<Value, NotFoundError> {
        match expr {
            // TODO should we canonicalize here?
            Expr::Var(var) => {
                if let Some(value) = ctx.get(var) {
                    Ok(*value)
                } else if let Some(f) = self.functions.get(var) {
                    assert!(f.schema.input.is_empty());
                    match f.nodes.get(&FunctionKey::from_vec(vec![])) {
                        Some(out) => Ok(out.value),
                        None => Err(NotFoundError(expr.clone())),
                    }
                } else {
                    Err(NotFoundError(expr.clone()))
                }
            }
            // Ok(ctx
            //     .get(var)
            //     .or_else(|| self.globals.get(var))
            //     .cloned()
            //     .unwrap_or_else(|| panic!("Couldn't find variable '{var}'"))),
            Expr::Lit(lit) => Ok(self.eval_lit(lit)),
            Expr::Call(op, args) => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.eval_expr(ctx, arg)?);
                }
                if let Some(function) = self.functions.get_mut(op) {
                    if let Some(out) = function.nodes.get(KeyRef::from_slice(values.as_slice())) {
                        Ok(out.value)
                    } else {
                        let ts = self.timestamp;
                        self.saturated = false;
                        let out = &function.schema.output;
                        match function.decl.default.as_ref() {
                            None if out.name() == "Unit".into() => {
                                function.insert(values, Value::unit(), ts);
                                Ok(Value::unit())
                            }
                            None if out.is_eq_sort() => {
                                let id = self.unionfind.make_set();
                                let value = Value::from_id(out.name(), id);
                                function.insert(values, value, ts);
                                Ok(value)
                            }
                            Some(default) => {
                                let default = default.clone(); // break the borrow
                                let value = self.eval_expr(ctx, &default)?;
                                let function = self.functions.get_mut(op).unwrap();
                                function.insert(values, value, ts);
                                Ok(value)
                            }
                            _ => panic!("invalid default for {:?}", function.decl.name),
                        }
                    }
                } else if let Some(prims) = self.primitives.get(op) {
                    let mut res = None;
                    for prim in prims.iter() {
                        // HACK
                        let types = values
                            .iter()
                            .map(|v| &*self.sorts[&v.tag])
                            .collect::<Vec<_>>();
                        if prim.accept(&types).is_some() {
                            if res.is_none() {
                                res = prim.apply(&values);
                            } else {
                                panic!("multiple implementation matches primitives {op}");
                            }
                        }
                    }
                    res.ok_or_else(|| NotFoundError(expr.clone()))
                } else {
                    panic!("Couldn't find function/primitive: {op}")
                }
            }
        }
    }

    fn print_function(&mut self, sym: Symbol, n: usize) -> Result<String, Error> {
        let f = self.functions.get(&sym).ok_or(TypeError::Unbound(sym))?;
        let schema = f.schema.clone();
        let nodes = f
            .nodes
            .iter()
            .take(n)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<_>>();

        let out_is_unit = f.schema.output.name() == "Unit".into();

        let mut buf = String::new();
        let s = &mut buf;
        for (ins, out) in nodes {
            write!(s, "({}", sym).unwrap();
            for (a, t) in ins.vals().iter().zip(&schema.input) {
                s.push(' ');
                let e = if t.is_eq_sort() {
                    self.extract(*a).1
                } else {
                    t.make_expr(*a)
                };
                write!(s, "{}", e).unwrap();
            }

            if out_is_unit {
                s.push(')');
            } else {
                let e = if schema.output.is_eq_sort() {
                    self.extract(out.value).1
                } else {
                    schema.output.make_expr(out.value)
                };
                write!(s, ") -> {}", e).unwrap();
            }
            s.push('\n');
            // write!(s, "{}(", self.decl.name)?;
            // for (i, arg) in args.iter().enumerate() {
            //     if i > 0 {
            //         write!(s, ", ")?;
            //     }
            //     write!(s, "{}", arg)?;
            // }
            // write!(s, ") = {}", value)?;
            // println!("{}", s);
        }

        Ok(buf)
    }

    pub fn print_size(&self, sym: Symbol) -> Result<String, Error> {
        let f = self.functions.get(&sym).ok_or(TypeError::Unbound(sym))?;
        Ok(format!("Function {} has size {}", sym, f.nodes.len()))
    }

    pub fn eval_closed_expr(&mut self, expr: &Expr) -> Result<Value, NotFoundError> {
        self.eval_expr(&Default::default(), expr)
    }

    pub fn run_rules(&mut self, limit: usize) -> [Duration; 3] {
        let mut search_time = Duration::default();
        let mut apply_time = Duration::default();

        // we might have to do a rebuild before starting,
        // because the use can manually do stuff
        let initial_rebuild_start = Instant::now();
        self.rebuild();
        let mut rebuild_time = initial_rebuild_start.elapsed();

        for i in 0..limit {
            self.saturated = true;
            let [st, at] = self.step_rules(i);
            search_time += st;
            apply_time += at;

            let rebuild_start = Instant::now();
            let updates = self.rebuild();
            log::info!("database size: {}", self.num_tuples());
            log::info!("Made {updates} updates",);
            rebuild_time += rebuild_start.elapsed();
            self.timestamp += 1;
            if self.saturated {
                log::info!("Breaking early at iteration {}!", i);
                break;
            }
        }

        // Report the worst offenders
        log::debug!("Slowest rules:\n{}", {
            let mut msg = String::new();
            let mut vec = self.rules.iter().collect::<Vec<_>>();
            vec.sort_by_key(|(_, r)| r.search_time + r.apply_time);
            for (name, rule) in vec.iter().rev().take(5) {
                write!(
                    msg,
                    "{name}\n  Search: {}\n  Apply: {}\n",
                    rule.search_time.as_secs_f64(),
                    rule.apply_time.as_secs_f64()
                )
                .unwrap();
            }
            msg
        });

        // // TODO detect functions
        // for (name, r) in &self.functions {
        //     log::debug!("{name}:");
        //     for (args, val) in &r.nodes {
        //         log::debug!("  {args:?} = {val:?}");
        //     }
        // }
        [search_time, apply_time, rebuild_time]
    }

    fn step_rules(&mut self, iteration: usize) -> [Duration; 2] {
        fn make_subst(rule: &Rule, values: &[Value]) -> Subst {
            let get_val = |t: &AtomTerm| match t {
                AtomTerm::Var(sym) => {
                    let i = rule
                        .query
                        .vars
                        .get_index_of(sym)
                        .unwrap_or_else(|| panic!("Couldn't find variable '{sym}'"));
                    values[i]
                }
                AtomTerm::Value(val) => *val,
            };

            rule.bindings
                .iter()
                .map(|(k, t)| (*k, get_val(t)))
                .collect()
        }

        let ban_length = 5;

        let mut rules = std::mem::take(&mut self.rules);
        let search_start = Instant::now();
        let mut searched = vec![];
        for (&name, rule) in rules.iter_mut() {
            let mut all_values = vec![];
            if rule.banned_until <= iteration {
                let rule_search_start = Instant::now();
                self.run_query(&rule.query, rule.todo_timestamp, |values| {
                    assert_eq!(values.len(), rule.query.vars.len());
                    all_values.extend_from_slice(values);
                });
                rule.todo_timestamp = self.timestamp;
                let rule_search_time = rule_search_start.elapsed();
                log::trace!(
                    "Searched for {name} in {} ({} results)",
                    rule_search_time.as_secs_f64(),
                    all_values.len()
                );
                rule.search_time += rule_search_time;
                searched.push((name, all_values));
            }
        }
        let search_elapsed = search_start.elapsed();

        let apply_start = Instant::now();
        'outer: for (name, all_values) in searched {
            let rule = rules.get_mut(&name).unwrap();
            let n = rule.query.vars.len();

            // backoff logic
            let len = all_values.len() / n;
            let threshold = self.match_limit << rule.times_banned;
            if len > threshold {
                rule.times_banned += 1;
                rule.banned_until = iteration + ban_length;
                log::info!("Banning rule {name} for {ban_length} iterations, matched {len} times");
                continue;
            }

            let rule_apply_start = Instant::now();

            for values in all_values.chunks(n) {
                rule.matches += 1;
                if rule.matches > 10_000_000 {
                    log::warn!("Rule {} has matched {} times, bailing!", name, rule.matches);
                    break 'outer;
                }
                let subst = make_subst(rule, values);
                log::trace!("Applying with {subst:?}");
                let _result: Result<_, _> = self.eval_actions(Some(subst), &rule.head);
            }

            rule.apply_time += rule_apply_start.elapsed();
        }
        self.rules = rules;
        let apply_elapsed = apply_start.elapsed();
        [search_elapsed, apply_elapsed]
    }

    fn add_rule_with_name(&mut self, name: String, rule: ast::Rule) -> Result<Symbol, Error> {
        let name = Symbol::from(name);
        let mut ctx = typecheck::Context::new(self);
        let (query0, bindings) = ctx.typecheck_query(&rule.body).map_err(Error::TypeErrors)?;
        let query = self.compile_gj_query(query0, ctx.types);
        let compiled_rule = Rule {
            query,
            bindings,
            head: rule.head,
            matches: 0,
            times_banned: 0,
            banned_until: 0,
            todo_timestamp: 0,
            search_time: Duration::default(),
            apply_time: Duration::default(),
        };
        match self.rules.entry(name) {
            Entry::Occupied(_) => panic!("Rule '{name}' was already present"),
            Entry::Vacant(e) => e.insert(compiled_rule),
        };
        Ok(name)
    }

    pub fn add_rule(&mut self, rule: ast::Rule) -> Result<Symbol, Error> {
        let name = format!("{}", rule);
        self.add_rule_with_name(name, rule)
    }

    pub fn clear_rules(&mut self) {
        self.rules = Default::default();
    }

    pub fn add_rewrite(&mut self, rewrite: ast::Rewrite) -> Result<Symbol, Error> {
        let name = format!("{} -> {}", rewrite.lhs, rewrite.rhs);
        let var = Symbol::from("__rewrite_var");
        let rule = ast::Rule {
            body: [Fact::Eq(vec![Expr::Var(var), rewrite.lhs])]
                .into_iter()
                .chain(rewrite.conditions)
                .collect(),
            head: vec![Action::Union(Expr::Var(var), rewrite.rhs)],
        };
        self.add_rule_with_name(name, rule)
    }

    fn run_command(&mut self, command: Command, should_run: bool) -> Result<String, Error> {
        Ok(match command {
            Command::Datatype { name, variants } => {
                self.declare_sort(name)?;
                for variant in variants {
                    self.declare_constructor(variant, name)?;
                }
                format!("Declared datatype {name}.")
            }
            Command::Sort(name, presort, args) => {
                // TODO extract this into a function
                assert!(!self.sorts.contains_key(&name));
                let mksort = self.presorts[&presort];
                let sort = mksort(self, name, &args)?;
                self.add_arcsort(sort);
                format!(
                    "Declared sort {name} = ({presort} {})",
                    ListDisplay(&args, " ")
                )
            }
            Command::Function(fdecl) => {
                self.declare_function(&fdecl)?;
                format!("Declared function {}.", fdecl.name)
            }
            Command::Rule(rule) => {
                let name = self.add_rule(rule)?;
                format!("Declared rule {name}.")
            }
            Command::Rewrite(rewrite) => {
                let name = self.add_rewrite(rewrite)?;
                format!("Declared rw {name}.")
            }
            Command::Run(limit) => {
                if should_run {
                    let [st, at, rt] = self.run_rules(limit);
                    let st = st.as_secs_f64();
                    let at = at.as_secs_f64();
                    let rt = rt.as_secs_f64();
                    let total = st + at + rt;
                    let size = self.num_tuples();
                    format!(
                        "Ran {limit} in {total:10.6}s.\n\
                        Search:  ({:.02}) {st:10.6}s\n\
                        Apply:   ({:.02}) {at:10.6}s\n\
                        Rebuild: ({:.02}) {rt:10.6}s\n\
                        Database size: {size}",
                        st / total,
                        at / total,
                        rt / total,
                    )
                } else {
                    log::info!("Skipping running!");
                    format!("Skipped run {limit}.")
                }
            }
            Command::Extract { e, variants } => {
                if should_run {
                    // TODO typecheck
                    self.rebuild();
                    let value = self.eval_closed_expr(&e)?;
                    log::info!("Extracting {e} at {value:?}");
                    let (cost, expr) = self.extract(value);
                    let mut msg = format!("Extracted with cost {cost}: {expr}");
                    if variants > 0 {
                        let exprs = self.extract_variants(value, variants);
                        let line = "\n    ";
                        let v_exprs = ListDisplay(&exprs, line);
                        write!(msg, "\nVariants of {expr}:{line}{v_exprs}").unwrap();
                    }
                    msg
                } else {
                    "Skipping extraction.".into()
                }
            }
            Command::Check(fact) => {
                if should_run {
                    self.check_with(&Default::default(), &fact)?;
                    "Checked.".into()
                } else {
                    "Skipping check.".into()
                }
            }
            Command::Action(action) => {
                if should_run {
                    self.eval_actions(None, std::slice::from_ref(&action))?;
                    format!("Run {action}.")
                } else {
                    format!("Skipping running {action}.")
                }
            }
            Command::Define { name, expr, cost } => {
                if should_run {
                    let value = self.eval_closed_expr(&expr)?;
                    let sort = self.sorts[&value.tag].clone();
                    self.declare_function(&FunctionDecl {
                        name,
                        schema: Schema {
                            input: vec![],
                            output: value.tag,
                        },
                        default: None,
                        merge: None,
                        cost,
                    })?;

                    let f = self.functions.get_mut(&name).unwrap();
                    f.insert(vec![], value, self.timestamp);
                    format!("Defined {name}: {sort:?}")
                } else {
                    format!("Skipping define {name}")
                }
            }
            Command::ClearRules => {
                self.clear_rules();
                "Clearing rules.".into()
            }
            Command::Query(_q) => {
                // let qsexp = sexp::Sexp::List(
                //     q.iter()
                //         .map(|fact| sexp::parse(&fact.to_string()).unwrap())
                //         .collect(),
                // );
                // let qcomp = self
                //     .compile_query(q)
                //     .unwrap_or_else(|_| panic!("Could not compile query"));
                // let mut res = vec![];
                // self.query(&qcomp, |v| {
                //     res.push(sexp::Sexp::List(
                //         v.iter()
                //             .map(|val| sexp::Sexp::Atom(sexp::Atom::S(format!("{}", val))))
                //             .collect(),
                //     ));
                // });
                // format!(
                //     "Query: {}\n  Bindings: {:?}\n  Results: {}",
                //     qsexp,
                //     qcomp,
                //     sexp::Sexp::List(res)
                // )
                todo!()
            }
            Command::Clear => {
                for f in self.functions.values_mut() {
                    f.nodes.clear();
                }
                "Cleared.".into()
            }
            Command::Push(n) => {
                (0..n).for_each(|_| self.push());
                format!("Pushed {n} levels.")
            }
            Command::Pop(n) => {
                for _ in 0..n {
                    self.pop()?;
                }
                format!("Popped {n} levels.")
            }
            Command::Print(f, n) => self.print_function(f, n)?,
            Command::PrintSize(f) => self.print_size(f)?,
            Command::Input { name, file } => {
                let func = self.functions.get_mut(&name).unwrap();
                let is_unit = func.schema.output.name().as_str() == "Unit";

                let mut filename = self.fact_directory.clone().unwrap_or_default();
                filename.push(file.as_str());

                // check that the function uses supported types
                for t in &func.schema.input {
                    match t.name().as_str() {
                        "i64" | "String" => {}
                        s => panic!("Unsupported type {} for input", s),
                    }
                }
                match func.schema.output.name().as_str() {
                    "i64" | "String" | "Unit" => {}
                    s => panic!("Unsupported type {} for input", s),
                }

                log::info!("Opening file '{:?}'...", filename);
                let mut f = File::open(filename).unwrap();
                let mut contents = String::new();
                f.read_to_string(&mut contents).unwrap();

                let mut actions: Vec<Action> = vec![];
                let mut str_buf: Vec<&str> = vec![];
                for line in contents.lines() {
                    str_buf.clear();
                    str_buf.extend(line.split('\t').map(|s| s.trim()));
                    if str_buf.is_empty() {
                        continue;
                    }

                    let parse = |s: &str| -> Expr {
                        if let Ok(i) = s.parse() {
                            Expr::Lit(Literal::Int(i))
                        } else {
                            Expr::Lit(Literal::String(s.into()))
                        }
                    };

                    let mut exprs: Vec<Expr> = str_buf.iter().map(|&s| parse(s)).collect();

                    actions.push(if is_unit {
                        Action::Expr(Expr::Call(name, exprs))
                    } else {
                        let out = exprs.pop().unwrap();
                        Action::Set(name, exprs, out)
                    });
                }
                self.eval_actions(None, &actions)?;
                format!("Read {} facts into {name} from '{file}'.", actions.len())
            }
        })
    }

    fn run_program(&mut self, program: Vec<Command>) -> Result<Vec<String>, Error> {
        let mut msgs = vec![];
        let should_run = true;

        for command in program {
            let msg = self.run_command(command, should_run)?;
            log::info!("{}", msg);
            msgs.push(msg);
        }

        Ok(msgs)
    }

    // this is bad because we shouldn't inspect values like this, we should use type information
    fn bad_find_value(&self, value: Value) -> Value {
        if let Some((tag, id)) = self.value_to_id(value) {
            Value::from_id(tag, self.find(id))
        } else {
            value
        }
    }

    pub fn parse_and_run_program(&mut self, input: &str) -> Result<Vec<String>, Error> {
        let parser = ast::parse::ProgramParser::new();
        let program = parser
            .parse(input)
            .map_err(|e| e.map_token(|tok| tok.to_string()))?;
        self.run_program(program)
    }

    pub fn num_tuples(&self) -> usize {
        self.functions.values().map(|f| f.nodes.len()).sum()
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    ParseError(#[from] lalrpop_util::ParseError<usize, String, String>),
    #[error(transparent)]
    NotFoundError(#[from] NotFoundError),
    #[error(transparent)]
    TypeError(#[from] TypeError),
    #[error("Errors:\n{}", ListDisplay(.0, "\n"))]
    TypeErrors(Vec<TypeError>),
    #[error("Check failed: {0:?} != {1:?}")]
    CheckError(Value, Value),
    #[error("Sort {0} already declared.")]
    SortAlreadyBound(Symbol),
    #[error("Tried to pop too much")]
    Pop,
}

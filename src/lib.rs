pub mod ast;
mod extract;
mod gj;
pub mod sort;
mod typecheck;
mod unionfind;
mod util;
mod value;

use hashbrown::hash_map::Entry;
use instant::{Duration, Instant};
use sort::*;
use thiserror::Error;

use ast::*;

use std::fmt::Write;
use std::fs::File;
use std::hash::Hash;
use std::io::Read;
use std::mem;
use std::ops::Deref;
use std::{fmt::Debug, sync::Arc};
use typecheck::{AtomTerm, Bindings};

type ArcSort = Arc<dyn Sort>;

pub use value::*;

use gj::*;

use unionfind::*;
use util::*;

use crate::typecheck::TypeError;

#[derive(Clone)]
pub struct Function {
    decl: FunctionDecl,
    schema: ResolvedSchema,
    nodes: FunctionData,
    updates: usize,
}

type FunctionTable = HashMap<Vec<Value>, Value>;

#[derive(Default, Clone)]
pub(crate) struct FunctionData {
    stable: FunctionTable,
    recent: FunctionTable,
    staging: Vec<(Vec<Value>, Value)>,
}

impl FunctionData {
    /// Whether there are any pending additions to FunctionData.
    ///
    /// We have this function around to catch bugs where queries are made
    /// against a function that assumes all tuples it owns reside in `stable`.
    pub(crate) fn stabilized(&self) -> bool {
        self.recent.is_empty() && self.staging.is_empty()
    }
    pub(crate) fn get(&self, args: &[Value]) -> Option<&Value> {
        self.stable.get(args)
    }
    pub(crate) fn insert(&mut self, args: Vec<Value>, ret: Value) -> Option<Value> {
        self.stable.insert(args, ret)
    }
    pub(crate) fn remove(&mut self, args: &[Value]) -> Option<Value> {
        assert!(self.stabilized());
        self.stable.remove(args)
    }
    pub(crate) fn len(&self) -> usize {
        assert!(self.stabilized());
        self.stable.len()
    }
    pub(crate) fn clear(&mut self) {
        self.stable.clear();
        self.recent.clear();
        self.staging.clear();
    }
    /// Move the contents of `stable` into `recent`. This should only be called
    /// when `recent` is empty.
    pub(crate) fn promote(&mut self) {
        debug_assert!(self.stabilized());
        mem::swap(&mut self.stable, &mut self.recent);
    }
    // do not submit
    // pub(crate) fn iter_all(&self) -> impl Iterator<Item=(&Vec<Value>, &Value)> {
    //     self.stable.iter().chain(self.recent.iter()).chain(self.staging.iter()
    // }
}

#[derive(Clone, Debug)]
struct ResolvedSchema {
    input: Vec<ArcSort>,
    output: ArcSort,
}

#[derive(Clone, Copy)]
enum InsertResult {
    None,
    Inserted,
    Merged,
}

impl InsertResult {
    fn changed(self) -> bool {
        match self {
            InsertResult::None => false,
            InsertResult::Inserted | InsertResult::Merged => true,
        }
    }
}

impl Function {
    fn canonicalize(&self, args: &mut [Value], val: &mut Value, uf: &mut UnionFind) -> bool {
        // XXX: do we have to register a delta when we update a value here?
        // I don't think that we do, only when we induce a union during a
        // rebuild.
        let mut changed = false;
        for (a, ty) in args.iter_mut().zip(&self.schema.input) {
            if ty.is_eq_sort() {
                let (next, new) = uf.find_mut_value_with_delta(*a);
                *a = next;
                changed |= new;
            }
        }
        if self.schema.output.is_eq_sort() {
            let (next, new) = uf.find_mut_value_with_delta(*val);
            *val = next;
            changed |= new;
        }
        changed
    }
    fn insert_and_merge(
        &self,
        map: &mut FunctionTable,
        uf: &mut UnionFind,
        args: Vec<Value>,
        mut value: Value,
    ) -> InsertResult {
        if self.schema.output.is_eq_sort() {
            value = uf.find_mut_value(value);
        }
        if self.schema.output.is_eq_sort() {
            let mut res = InsertResult::Inserted;
            map.entry(args)
                .and_modify(|value2| {
                    let was = value.bits;
                    *value2 = uf.union_values(value, *value2);
                    res = if value2.bits == was {
                        InsertResult::None
                    } else {
                        InsertResult::Merged
                    };
                })
                .or_insert_with(|| uf.find_mut_value(value));
            res
        } else {
            let was = map
                .entry(args)
                // .and_modify(|value2| *value2 = uf.union_values(value.clone(), value2.clone()))
                .or_insert(value);
            if was == &value {
                InsertResult::None
            } else {
                InsertResult::Inserted
            }
        }
    }
    fn insert_and_merge_maybe_promote(
        &self,
        stable: &mut FunctionTable,
        recent: &mut FunctionTable,
        uf: &mut UnionFind,
        args: Vec<Value>,
        value: Value,
        target_recent: bool,
    ) -> bool {
        match (target_recent, self.schema.output.is_eq_sort()) {
            (true, true) => {
                if let Some(prev) = stable.get_mut(&args) {
                    if uf.union_values_with_delta(prev, value) {
                        // We've changed the value. Time to promote
                        let value = *prev;
                        stable.remove(&args);
                        self.insert_and_merge(recent, uf, args, value);
                        true
                    } else {
                        // This tuple was already present in `stable`. Nothing's
                        // changed.
                        false
                    }
                } else {
                    // Not present in stable. target_recent=true so we'll go
                    // ahead and insert into recent
                    self.insert_and_merge(recent, uf, args, value).changed()
                }
            }
            (true, false) => {
                if stable.contains_key(&args) {
                    // We don't attempt to merge non-eq-sort values. If this is
                    // present in stable we'll just continue on.
                    return false;
                }
                // target_recent=true, so we attempt to insert into recent.
                self.insert_and_merge(recent, uf, args, value).changed()
            }
            (false, true) => {
                if let Some(prev) = stable.get_mut(&args) {
                    if uf.union_values_with_delta(prev, value) {
                        // We've changed the value. Time to promote
                        let value = *prev;
                        stable.remove(&args);
                        self.insert_and_merge(recent, uf, args, value);
                        true
                    } else {
                        // This tuple was already present in `stable`. Nothing's
                        // changed.
                        false
                    }
                } else if let Some(prev) = recent.get_mut(&args) {
                    // If this is already in recent, we want to merge the value
                    // and then be done. The only time we move a tuple from
                    // recent into stable is during an update.
                    uf.union_values_with_delta(prev, value)
                } else {
                    // Not present in stable or recent. target_recent=false so we'll go
                    // ahead and insert into stable
                    self.insert_and_merge(stable, uf, args, value).changed()
                }
            }
            (false, false) => {
                if recent.contains_key(&args) {
                    // We don't attempt to merge non-eq-sort values. If this is
                    // present in recent we'll just continue on.
                    return false;
                }
                // target_recent=false, so we attempt to insert into stable.
                self.insert_and_merge(stable, uf, args, value).changed()
            }
        }
    }
    pub(crate) fn start_rebuild_seminaive(&mut self, uf: &mut UnionFind) -> bool {
        let mut changed = false;
        let mut stable = mem::take(&mut self.nodes.stable);
        let mut new_stable = Default::default();
        let mut recent = mem::take(&mut self.nodes.recent);
        let mut new_recent = Default::default();
        let mut staging = mem::take(&mut self.nodes.staging);
        for (mut args, mut value) in stable.drain() {
            changed |= if self.canonicalize(&mut args, &mut value, uf) {
                // We changed during canonicalization: target the recent map.
                self.insert_and_merge_maybe_promote(
                    &mut new_stable,
                    &mut new_recent,
                    uf,
                    args,
                    value,
                    true,
                );
                true
            } else {
                self.insert_and_merge_maybe_promote(
                    &mut new_stable,
                    &mut new_recent,
                    uf,
                    args,
                    value,
                    false,
                )
            };
        }
        for (mut args, mut value) in recent.drain() {
            changed |= self.canonicalize(&mut args, &mut value, uf);
            // unconditionally target `recent`
            changed |= self.insert_and_merge_maybe_promote(
                &mut new_stable,
                &mut new_recent,
                uf,
                args,
                value,
                true,
            );
        }
        for (mut args, mut value) in staging.drain(..) {
            self.canonicalize(&mut args, &mut value, uf);
            changed |= self.insert_and_merge_maybe_promote(
                &mut new_stable,
                &mut new_recent,
                uf,
                args,
                value,
                true,
            );
        }
        self.nodes.stable = new_stable;
        self.nodes.recent = new_recent;
        self.nodes.staging = staging;
        // TODO: pool the memory for maps.
        changed
    }
    pub(crate) fn continue_rebuild_seminaive(&mut self, uf: &mut UnionFind) -> bool {
        debug_assert!(self.nodes.staging.is_empty());
        let mut changed = false;
        let mut stable = mem::take(&mut self.nodes.stable);
        let mut new_stable = Default::default();
        let mut recent = mem::take(&mut self.nodes.recent);
        let mut new_recent = Default::default();
        for (mut args, mut value) in stable.drain() {
            changed |= if self.canonicalize(&mut args, &mut value, uf) {
                // We changed during canonicalization: target the recent map.
                self.insert_and_merge_maybe_promote(
                    &mut new_stable,
                    &mut new_recent,
                    uf,
                    args,
                    value,
                    true,
                );
                true
            } else {
                self.insert_and_merge_maybe_promote(
                    &mut new_stable,
                    &mut new_recent,
                    uf,
                    args,
                    value,
                    false,
                )
            };
        }
        for (mut args, mut value) in recent.drain() {
            changed |= self.canonicalize(&mut args, &mut value, uf);
            // unconditionally target `recent`
            changed |= self.insert_and_merge_maybe_promote(
                &mut new_stable,
                &mut new_recent,
                uf,
                args,
                value,
                true,
            );
        }
        self.nodes.stable = new_stable;
        self.nodes.recent = new_recent;
        changed
    }
    pub fn rebuild_naive(&mut self, uf: &mut UnionFind) -> usize {
        // FIXME this doesn't compute updates properly
        let n_unions = uf.n_unions();
        let old_nodes = mem::take(&mut self.nodes);
        let mut new_stable = HashMap::default();
        for (mut args, mut value) in old_nodes.stable {
            self.canonicalize(&mut args, &mut value, uf);
            self.insert_and_merge(&mut new_stable, uf, args, value);
        }
        self.nodes.stable = new_stable;
        uf.n_unions() - n_unions + std::mem::take(&mut self.updates)
    }
    pub(crate) fn promote(&mut self) {
        self.nodes.promote()
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
    pub match_limit: usize,
}

#[derive(Clone, Debug)]
struct Rule {
    query: CompiledQuery,
    bindings: Bindings,
    head: Vec<Action>,
    matches: usize,
    times_banned: usize,
    banned_until: usize,
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
            for (inputs, output) in function
                .nodes
                .stable
                .iter()
                .chain(function.nodes.recent.iter())
            {
                for input in inputs {
                    assert_eq!(
                        input,
                        &self.bad_find_value(*input),
                        "{name}({inputs:?}) = {output:?}\n{:?}",
                        function.schema,
                    )
                }
                assert_eq!(
                    output,
                    &self.bad_find_value(*output),
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
                    let old_value = function.nodes.insert(values.clone(), value);

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
                                    self.functions
                                        .get_mut(f)
                                        .unwrap()
                                        .nodes
                                        .insert(values, new_value);
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
                    function.nodes.remove(&values);
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
                        self.rebuild_naive();
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
                            .get(&values)
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

    pub fn rebuild_naive(&mut self) -> usize {
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

    pub fn rebuild_seminaive(&mut self) -> bool /* changed */ {
        let mut changed = false;
        for f in self.functions.values_mut() {
            changed |= f.start_rebuild_seminaive(&mut self.unionfind);
        }
        if !changed {
            return false;
        }
        loop {
            // We need a separate variable to capture changes introduced by the
            // rebuilding loop. Rebuilding needs to converge even if we report a
            // change back to the outer iteration loop indicating that we
            // accumulated nontrivial deltas in this iteration of the rules.
            let mut local_changed = false;
            for f in self.functions.values_mut() {
                local_changed |= f.continue_rebuild_seminaive(&mut self.unionfind);
            }
            changed |= local_changed;
            if !local_changed {
                break;
            }
        }
        changed
    }

    fn rebuild_one(&mut self) -> usize {
        let mut new_unions = 0;
        for function in self.functions.values_mut() {
            new_unions += function.rebuild_naive(&mut self.unionfind);
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
            updates: 0,
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
                    f.nodes
                        .get(&[])
                        .copied()
                        .ok_or_else(|| NotFoundError(expr.clone()))
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
                    if let Some(value) = function.nodes.get(&values) {
                        Ok(*value)
                    } else {
                        let out = &function.schema.output;
                        match function.decl.default.as_ref() {
                            None if out.name() == "Unit".into() => {
                                function.nodes.insert(values, Value::unit());
                                Ok(Value::unit())
                            }
                            None if out.is_eq_sort() => {
                                let id = self.unionfind.make_set();
                                let value = Value::from_id(out.name(), id);
                                function.nodes.insert(values, value);
                                Ok(value)
                            }
                            Some(default) => {
                                let default = default.clone(); // break the borrow
                                let value = self.eval_expr(ctx, &default)?;
                                let function = self.functions.get_mut(op).unwrap();
                                function.nodes.insert(values, value);
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
        debug_assert!(f.nodes.stabilized());
        let nodes = f
            .nodes
            .stable
            .iter()
            .take(n)
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>();

        let out_is_unit = f.schema.output.name() == "Unit".into();

        let mut buf = String::new();
        let s = &mut buf;
        for (ins, out) in nodes {
            write!(s, "({}", sym).unwrap();
            for (a, t) in ins.iter().zip(&schema.input) {
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
                    self.extract(out).1
                } else {
                    schema.output.make_expr(out)
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

    pub fn eval_closed_expr(&mut self, expr: &Expr) -> Result<Value, NotFoundError> {
        self.eval_expr(&Default::default(), expr)
    }

    pub fn run_rules(&mut self, limit: usize, mut opts: ExecOptions) -> [Duration; 3] {
        let mut search_time = Duration::default();
        let mut apply_time = Duration::default();
        let mut rebuild_time = Duration::default();
        if limit == 1 {
            opts.seminaive = false;
        }
        for i in 0..limit {
            let [st, at] = if opts.seminaive {
                self.step_rules_seminaive(i)
            } else {
                self.step_rules_naive(i)
            };
            search_time += st;
            apply_time += at;

            let rebuild_start = Instant::now();
            if !opts.seminaive {
                let updates = self.rebuild_naive();
                log::debug!("Made {updates} updates",);
                continue;
            }
            // Seminaive
            let changed = self.rebuild_seminaive();
            rebuild_time += rebuild_start.elapsed();
            if !changed {
                log::debug!("breaking early");
                break;
            }
            // if updates == 0 {
            //     log::debug!("Breaking early!");
            //     break;
            // }
        }

        // TODO detect functions
        if log::log_enabled!(log::Level::Debug) {
            for (name, r) in &self.functions {
                log::debug!("{name}/stable:");
                for (args, val) in &r.nodes.stable {
                    log::debug!("  {args:?} = {val:?}");
                }
                log::debug!("{name}/recent:");
                for (args, val) in &r.nodes.recent {
                    log::debug!("  {args:?} = {val:?}");
                }
                log::debug!("{name}/staged:");
                for (args, val) in &r.nodes.staging {
                    log::debug!("  {args:?} = {val:?}");
                }
            }
        }
        [search_time, apply_time, rebuild_time]
    }

    fn step_rules_naive(&mut self, iteration: usize) -> [Duration; 2] {
        let ban_length = 5;

        let search_start = Instant::now();
        let mut searched = vec![];
        for rule in self.rules.values() {
            let mut all_values = vec![];
            if rule.banned_until <= iteration {
                self.run_query(&rule.query, false, |values| {
                    assert_eq!(values.len(), rule.query.vars.len());
                    all_values.extend_from_slice(values);
                });
            }
            searched.push(all_values);
        }
        let search_elapsed = search_start.elapsed();

        let apply_start = Instant::now();
        let mut rules = std::mem::take(&mut self.rules);
        'outer: for ((name, rule), all_values) in rules.iter_mut().zip(searched) {
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
        }
        self.rules = rules;
        let apply_elapsed = apply_start.elapsed();
        [search_elapsed, apply_elapsed]
    }

    fn step_rules_seminaive(&mut self, iteration: usize) -> [Duration; 2] {
        // NB: no backoffs to start with, but we can implement them
        // "hierarchically" if we want to add them back.
        // * Want to override "insert" actions
        if iteration == 0 {
            // promote values in all (relevant?) functions stable=>recent. We'll
            // scan them all in the first iteration.
            for f in self.egraphs.last_mut().unwrap().functions.values_mut() {
                f.promote();
            }
        }
        let search_start = Instant::now();
        let mut searched = vec![];
        for rule in self.rules.values() {
            let mut all_values = vec![];
            self.run_query(&rule.query, false, |values| {
                assert_eq!(values.len(), rule.query.vars.len());
                all_values.extend_from_slice(values);
            });
            searched.push(all_values);
        }
        let search_elapsed = search_start.elapsed();
        let apply_start = Instant::now();
        let mut rules = std::mem::take(&mut self.rules);
        for (rule, all_values) in rules.values_mut().zip(searched) {
            let n = rule.query.vars.len();
            for values in all_values.chunks(n) {
                rule.matches += 1;
                let subst = make_subst(rule, values);
                log::trace!("[seminaive] Applying with {subst:?}");
                let _result: Result<_, _> = self.eval_actions(Some(subst), &rule.head);
            }
        }
        self.rules = rules;

        let apply_elapsed = apply_start.elapsed();
        [search_elapsed, apply_elapsed]
    }

    fn add_rule_with_name(&mut self, name: String, rule: ast::Rule) -> Result<Symbol, Error> {
        let name = Symbol::from(name);
        let mut ctx = typecheck::Context::new(self);
        let (atoms, bindings) = ctx.typecheck_query(&rule.body).map_err(Error::TypeErrors)?;
        let query = self.compile_gj_query(atoms, ctx.types);
        let compiled_rule = Rule {
            query,
            bindings,
            head: rule.head,
            matches: 0,
            times_banned: 0,
            banned_until: 0,
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

    fn for_each_canonicalized(&self, name: Symbol, recent: bool, mut cb: impl FnMut(&[Value])) {
        let mut ids = vec![];
        let f = self
            .functions
            .get(&name)
            .unwrap_or_else(|| panic!("No function {name}"));
        for (children, value) in if recent {
            &f.nodes.recent
        } else {
            &f.nodes.stable
        } {
            ids.clear();
            // FIXME canonicalize, do we need to with rebuilding?
            // ids.extend(children.iter().map(|id| self.find(value)));
            ids.extend(children.iter().cloned());
            ids.push(*value);
            cb(&ids);
        }
    }

    fn run_command(
        &mut self,
        command: Command,
        should_run: bool,
        opts: ExecOptions,
    ) -> Result<String, Error> {
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
                    let [st, at, rt] = self.run_rules(limit, opts);
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
                    self.rebuild_naive();
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
                    f.nodes.insert(vec![], value);
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
            Command::Input { name, file } => {
                let func = self.functions.get_mut(&name).unwrap();
                let is_unit = func.schema.output.name().as_str() == "Unit";

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

                log::info!("Opening file '{}'...", file);
                let mut f = File::open(file.as_str()).unwrap();
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

    fn run_program(
        &mut self,
        program: Vec<Command>,
        opts: ExecOptions,
    ) -> Result<Vec<String>, Error> {
        let mut msgs = vec![];
        let should_run = true;

        for command in program {
            let msg = self.run_command(command, should_run, opts)?;
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

    pub fn parse_and_run_program(
        &mut self,
        input: &str,
        opts: ExecOptions,
    ) -> Result<Vec<String>, Error> {
        let parser = ast::parse::ProgramParser::new();
        let program = parser
            .parse(input)
            .map_err(|e| e.map_token(|tok| tok.to_string()))?;
        self.run_program(program, opts)
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

#[derive(Default, Clone, Copy)]
pub struct ExecOptions {
    pub seminaive: bool,
}

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

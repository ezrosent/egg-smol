use indexmap::map::Entry;
use smallvec::SmallVec;

use crate::{
    typecheck::{Atom, AtomTerm, Query},
    *,
};
use std::{cell::UnsafeCell, cmp, fmt::Debug, ops::Range};

enum Instr<'a> {
    Intersect {
        value_idx: usize,
        trie_accesses: Vec<(usize, TrieAccess<'a>)>,
    },
    Call {
        prim: Primitive,
        args: Vec<AtomTerm>,
        check: bool, // check or assign to output variable
    },
}

struct Program<'a>(Vec<Instr<'a>>);

impl<'a> std::fmt::Display for Program<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for instr in &self.0 {
            match instr {
                Instr::Intersect {
                    value_idx,
                    trie_accesses,
                } => {
                    write!(f, " Intersect @ {} ", value_idx)?;
                    for (trie_idx, a) in trie_accesses {
                        write!(f, "  {}: {}", trie_idx, a)?;
                    }
                    writeln!(f)?
                }
                Instr::Call { prim, args, check } => {
                    writeln!(f, " Call {:?} {:?} {:?}", prim, args, check)?;
                }
            }
        }
        Ok(())
    }
}

struct Context<'b> {
    query: &'b CompiledQuery,
    tuple: Vec<Value>,
    matches: usize,
}

impl<'b> Context<'b> {
    fn new(
        egraph: &'b EGraph,
        cq: &'b CompiledQuery,
        timestamp_ranges: &[Range<u32>],
    ) -> Option<(Self, Program<'b>, Vec<Symbol>)> {
        let ctx = Context {
            query: cq,
            tuple: vec![Value::fake(); cq.vars.len()],
            matches: 0,
        };

        let (program, vars) = egraph.compile_program(cq, timestamp_ranges)?;

        Some((ctx, program, vars))
    }

    fn eval<F>(&mut self, tries: &mut [&LazyTrie], program: &[Instr], f: &mut F)
    where
        F: FnMut(&[Value]),
    {
        let (instr, program) = match program.split_first() {
            None => {
                self.matches += 1;
                return f(&self.tuple);
            }
            Some(pair) => pair,
        };

        match instr {
            Instr::Intersect {
                value_idx,
                trie_accesses,
            } => {
                #[cfg(feature = "dhat-ad-hoc")]
                dhat::ad_hoc_event(trie_accesses.len());
                match trie_accesses.as_slice() {
                    [(j, access)] => tries[*j].for_each(access, |value, trie| {
                        let old_trie = std::mem::replace(&mut tries[*j], trie);
                        self.tuple[*value_idx] = value;
                        self.eval(tries, program, f);
                        tries[*j] = old_trie;
                    }),
                    [a, b] => {
                        let (a, b) = if tries[a.0].len() <= tries[b.0].len() {
                            (a, b)
                        } else {
                            (b, a)
                        };
                        tries[a.0].for_each(&a.1, |value, ta| {
                            if let Some(tb) = tries[b.0].get(&b.1, value) {
                                let old_ta = std::mem::replace(&mut tries[a.0], ta);
                                let old_tb = std::mem::replace(&mut tries[b.0], tb);
                                self.tuple[*value_idx] = value;
                                self.eval(tries, program, f);
                                tries[a.0] = old_ta;
                                tries[b.0] = old_tb;
                            }
                        })
                    }
                    _ => {
                        let (j_min, access_min) = trie_accesses
                            .iter()
                            .min_by_key(|(j, _a)| tries[*j].len())
                            .unwrap();

                        let mut new_tries = tries.to_vec();

                        tries[*j_min].for_each(access_min, |value, min_trie| {
                            new_tries[*j_min] = min_trie;
                            for (j, access) in trie_accesses {
                                if j != j_min {
                                    if let Some(t) = tries[*j].get(access, value) {
                                        new_tries[*j] = t;
                                    } else {
                                        return;
                                    }
                                }
                            }

                            // at this point, new_tries is ready to go
                            self.tuple[*value_idx] = value;
                            self.eval(&mut new_tries, program, f);
                        });
                    }
                }
            }
            Instr::Call { prim, args, check } => {
                let (out, args) = args.split_last().unwrap();
                let mut values: Vec<Value> = vec![];
                for arg in args {
                    values.push(match arg {
                        AtomTerm::Var(v) => {
                            let i = self.query.vars.get_index_of(v).unwrap();
                            self.tuple[i]
                        }
                        AtomTerm::Value(val) => *val,
                    })
                }

                if let Some(res) = prim.apply(&values) {
                    match out {
                        AtomTerm::Var(v) => {
                            let i = self.query.vars.get_index_of(v).unwrap();
                            if *check && self.tuple[i] != res {
                                return;
                            }
                            self.tuple[i] = res;
                        }
                        AtomTerm::Value(val) => {
                            assert!(check);
                            if val != &res {
                                return;
                            }
                        }
                    }
                    self.eval(tries, program, f);
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub(crate) enum Constraint {
    Eq(usize, usize),
    Const(usize, Value),
}

impl Constraint {
    fn check(&self, tuple: &[Value], out: Value) -> bool {
        let get = |i: usize| {
            if i < tuple.len() {
                &tuple[i]
            } else {
                debug_assert_eq!(i, tuple.len());
                &out
            }
        };
        match self {
            Constraint::Eq(i, j) => get(*i) == get(*j),
            Constraint::Const(i, t) => get(*i) == t,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct VarInfo {
    /// indexes into the `atoms` field of CompiledQuery
    occurences: Vec<usize>,
}

type VarMap = IndexMap<Symbol, VarInfo>;

#[derive(Debug, Clone)]
pub struct CompiledQuery {
    query: Query,
    pub vars: VarMap,
}

impl EGraph {
    pub(crate) fn compile_gj_query(
        &self,
        query: Query,
        _types: HashMap<Symbol, ArcSort>,
    ) -> CompiledQuery {
        // NOTE: this vars order only used for ordering the tuple,
        // It is not the GJ variable order.
        let mut vars: IndexMap<Symbol, VarInfo> = Default::default();
        for (i, atom) in query.atoms.iter().enumerate() {
            for v in atom.vars() {
                // only count grounded occurrences
                vars.entry(v).or_default().occurences.push(i)
            }
        }

        for prim in &query.filters {
            for v in prim.vars() {
                vars.entry(v).or_default();
            }
        }

        CompiledQuery { query, vars }
    }

    fn make_trie_access(
        &self,
        var: Symbol,
        atom: &Atom<Symbol>,
        timestamp_range: Range<u32>,
    ) -> TrieAccess {
        let column = atom
            .args
            .iter()
            .position(|arg| arg == &AtomTerm::Var(var))
            .unwrap();

        let function = &self.functions[&atom.head];

        let mut constraints = vec![];
        for (i, t) in atom.args.iter().enumerate() {
            match t {
                AtomTerm::Value(val) => constraints.push(Constraint::Const(i, *val)),
                AtomTerm::Var(_v) => {
                    if let Some(j) = atom.args[..i].iter().position(|t2| t == t2) {
                        constraints.push(Constraint::Eq(j, i));
                    }
                }
            }
        }

        TrieAccess {
            function,
            timestamp_range,
            column,
            constraints,
        }
    }

    fn compile_program(
        &self,
        query: &CompiledQuery,
        timestamp_ranges: &[Range<u32>],
    ) -> Option<(Program, Vec<Symbol>)> {
        #[derive(Default)]
        struct VarInfo2 {
            occurences: Vec<usize>,
            intersected_on: usize,
            size_guess: usize,
        }

        let atoms = &query.query.atoms;
        let mut vars: IndexMap<Symbol, VarInfo2> = Default::default();
        for (i, atom) in atoms.iter().enumerate() {
            for v in atom.vars() {
                vars.entry(v).or_default().occurences.push(i)
            }
        }

        let relation_sizes: Vec<usize> = atoms
            .iter()
            .zip(timestamp_ranges)
            .map(|(atom, range)| self.functions[&atom.head].get_size(range))
            .collect();

        if relation_sizes.iter().any(|&s| s == 0) {
            return None;
        }

        for (_v, info) in &mut vars {
            assert!(!info.occurences.is_empty());
            info.size_guess = info
                .occurences
                .iter()
                .map(|&i| relation_sizes[i])
                .min()
                .unwrap();
            // info.size_guess >>= info.occurences.len() - 1;
        }

        let mut ordered_vars = IndexMap::default();
        while !vars.is_empty() {
            let (&var, _info) = vars
                .iter()
                .max_by_key(|(_v, info)| {
                    let size = info.size_guess as isize;
                    (info.occurences.len(), info.intersected_on, -size)
                })
                .unwrap();

            let info = vars.remove(&var).unwrap();
            for &i in &info.occurences {
                for v in atoms[i].vars() {
                    if let Some(info) = vars.get_mut(&v) {
                        info.intersected_on += 1;
                    }
                }
            }

            ordered_vars.insert(var, info);
        }
        vars = ordered_vars;

        let mut program: Vec<Instr> = vars
            .iter()
            .map(|(&v, info)| {
                let idx = query.vars.get_index_of(&v).unwrap();
                Instr::Intersect {
                    value_idx: idx,
                    trie_accesses: info
                        .occurences
                        .iter()
                        .map(|&atom_idx| {
                            let atom = &atoms[atom_idx];
                            let range = timestamp_ranges[atom_idx].clone();
                            let access = self.make_trie_access(v, atom, range);
                            (atom_idx, access)
                        })
                        .collect(),
                }
            })
            .collect();

        // now we can try to add primitives
        // TODO this is very inefficient, since primitives all at the end
        let mut extra = query.query.filters.clone();
        while !extra.is_empty() {
            let next = extra.iter().position(|p| {
                assert!(!p.args.is_empty());
                p.args[..p.args.len() - 1].iter().all(|a| match a {
                    AtomTerm::Var(v) => vars.contains_key(v),
                    AtomTerm::Value(_) => true,
                })
            });

            if let Some(i) = next {
                let p = extra.remove(i);
                let check = match p.args.last().unwrap() {
                    AtomTerm::Var(v) => match vars.entry(*v) {
                        Entry::Occupied(_) => true,
                        Entry::Vacant(e) => {
                            e.insert(Default::default());
                            false
                        }
                    },
                    AtomTerm::Value(_) => true,
                };
                program.push(Instr::Call {
                    prim: p.head.clone(),
                    args: p.args.clone(),
                    check,
                });
            } else {
                panic!("cycle")
            }
        }

        Some((Program(program), vars.into_keys().collect()))
    }

    pub(crate) fn run_query<F>(&self, cq: &CompiledQuery, timestamp: u32, mut f: F)
    where
        F: FnMut(&[Value]),
    {
        log::trace!("RUN QUERY ts={timestamp}");
        let has_atoms = !cq.query.atoms.is_empty();

        // for the later atoms, we consider everything
        let mut timestamp_ranges = vec![0..u32::MAX; cq.query.atoms.len()];
        // let cached_ranges: Vec<Option<Rc<LazyTrie>>> = cq
        //     .query
        //     .atoms
        //     .iter()
        //     .map(|x| {
        //         self.functions[&x.head].fetch_cached_index(
        //             TrieSpec {
        //                 columns: todo!(),
        //                 constraints: todo!(),
        //             },
        //             0..u32::MAX,
        //         )
        //     })
        //     .collect();
        if has_atoms {
            let mut scratch_tmp_tries = Vec::new();
            let mut scratch_cached_tries = Vec::new();
            let mut scratch_writes = Vec::new();
            let do_seminaive = true;
            for (atom_i, atom) in cq.query.atoms.iter().enumerate() {
                // this time, we only consider "new stuff" for this atom
                if do_seminaive {
                    timestamp_ranges[atom_i] = timestamp..u32::MAX;
                }

                // do the gj
                if let Some((mut ctx, program, vars)) = Context::new(self, cq, &timestamp_ranges) {
                    scratch_tmp_tries.clear();
                    scratch_cached_tries.clear();
                    scratch_writes.clear();
                    let mut trie_refs = Vec::with_capacity(cq.query.atoms.len());
                    log::debug!(
                        "Query: {}\nNew atom: {}\nVars: {}\nProgram\n{}",
                        cq.query,
                        atom,
                        ListDisplay(cq.vars.keys(), " "),
                        program
                    );
                    for (atom, range) in cq.query.atoms.iter().zip(timestamp_ranges.iter()) {
                        let f = self.functions.get(&atom.head).unwrap();
                        let spec = TrieSpec::new(vars.iter().filter_map(|var| {
                            atom.args
                                .iter()
                                .position(|x| x == &AtomTerm::Var(*var))
                                .map(|x| x as u32)
                        }));
                        if let Some(trie) = f.fetch_cached_index(spec, range.clone()) {
                            scratch_writes.push((true, scratch_cached_tries.len()));
                            scratch_cached_tries.push(trie);
                        } else {
                            scratch_writes.push((false, scratch_tmp_tries.len()));
                            let new_trie = LazyTrie::new();
                            new_trie.add_pending(
                                f.timestamp_range_to_index_range(range.clone())
                                    .map(|x| x as RowIdx),
                            );
                            scratch_tmp_tries.push(new_trie);
                        }
                    }
                    log::trace!(
                        "scratch_writes={scratch_writes:?}, ranges={:?}",
                        cq.query
                            .atoms
                            .iter()
                            .map(|x| x.head)
                            .zip(timestamp_ranges.iter())
                            .collect::<Vec<_>>()
                    );
                    trie_refs.extend(scratch_writes.iter().map(|(cached, index)| {
                        if *cached {
                            &*scratch_cached_tries[*index]
                        } else {
                            &scratch_tmp_tries[*index]
                        }
                    }));
                    // Want to look up the cached tries on the fly here.
                    // Backing `tries` in a smallvec for anything that we can't
                    // cache, then grab the rcs, insert into trie_refs in
                    // sequence. Need to compute variable order and we're good?
                    // Where do the constraints come in.
                    ctx.eval(&mut trie_refs, &program.0, &mut f);
                    log::debug!("Matched {} times", ctx.matches);
                }

                if !do_seminaive {
                    break;
                }

                // now we can fix this atom to be "old stuff" only
                // range is half-open; timestamp is excluded
                timestamp_ranges[atom_i] = 0..timestamp;
            }
        } else if let Some((mut ctx, program, _)) = Context::new(self, cq, &[]) {
            let tries = LazyTrie::make_initial_vec(&timestamp_ranges);
            let mut trie_refs = tries.iter().collect::<Vec<_>>();
            ctx.eval(&mut trie_refs, &program.0, &mut f)
        }
    }
}

#[derive(Copy, Clone)]
struct CopyRange {
    start: u32,
    end: u32,
}

impl From<CopyRange> for Range<u32> {
    fn from(cr: CopyRange) -> Self {
        cr.start..cr.end
    }
}
impl From<Range<u32>> for CopyRange {
    fn from(x: Range<u32>) -> Self {
        CopyRange {
            start: x.start,
            end: x.end,
        }
    }
}

pub(crate) struct ManagedTrie {
    ts_range: Cell<CopyRange>,
    trie: Rc<LazyTrie>,
}

impl Default for ManagedTrie {
    fn default() -> ManagedTrie {
        ManagedTrie {
            ts_range: Cell::new((0..0).into()),
            trie: Rc::new(LazyTrie::new()),
        }
    }
}

impl ManagedTrie {
    pub(crate) fn access_at(&self, f: &Function, ts_range: Range<u32>) -> Rc<LazyTrie> {
        // TODO: _Just_ read the indexes out and insert them into pending.
        // * enum => struct for LazyTrieData
        // * ignore timestamp in LazyTrieInner  and eventually get rid of it (or rename LazyTrieData)
        // * force now just checks for nonempty 'delayed'; this actually makes it more uniform
        log::trace!(
            "access={ts_range:?}, cur={:?}",
            Range::from(self.ts_range.get())
        );
        let (diff, new) = range_diff(self.ts_range.get().into(), ts_range);
        log::trace!("diff={diff:?}, new={new:?}");
        let pending = f.timestamp_range_to_index_range(diff);
        self.ts_range.set(new.into());
        self.trie.add_pending(pending.map(|x| x as RowIdx));
        log::trace!("accessing trie at {:?}", self.trie);
        self.trie.clone()
    }
}

pub(crate) struct LazyTrie(UnsafeCell<LazyTrieInner>);

impl std::fmt::Debug for LazyTrie {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe { (&*self.0.get()).fmt(f) }
    }
}

// TODO collapse inner and data
struct LazyTrieInner {
    data: LazyTrieData,
}

impl std::fmt::Debug for LazyTrieInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

#[derive(Debug)]
struct LazyTrieData {
    delayed: SmallVec<[u32; 4]>,
    data: SparseMap,
}

type SparseMap = HashMap<Value, LazyTrie>;

type RowIdx = u32;
impl LazyTrie {
    // CPS wrappers around the interiorly-mutable data: you can still abuse
    // this, but this makes it harder to accidentally introduce an alias.

    unsafe fn with_mut_data<R>(&self, f: impl FnOnce(&mut LazyTrieData) -> R) -> R {
        f(&mut (*self.0.get()).data)
    }
    unsafe fn with_mut_inner<R>(&self, mut f: impl FnMut(&mut LazyTrieInner) -> R) -> R {
        f(&mut *self.0.get())
    }
    // TODO: remove
    fn make_initial_vec(ranges: &[Range<u32>]) -> Vec<Self> {
        ranges.iter().cloned().map(|_| LazyTrie::new()).collect()
    }

    fn add_pending(&self, pending: impl Iterator<Item = RowIdx>) {
        unsafe { self.with_mut_data(move |f| f.delayed.extend(pending)) }
    }

    pub(crate) fn new() -> LazyTrie {
        LazyTrie(UnsafeCell::new(LazyTrieInner {
            data: LazyTrieData {
                delayed: Default::default(),
                data: Default::default(),
            },
        }))
    }

    fn len(&self) -> usize {
        unsafe { self.with_mut_data(|data| data.data.len() + data.delayed.len()) }
    }

    fn force(&self, access: &TrieAccess) -> &LazyTrieInner {
        unsafe {
            self.with_mut_inner(|this| {
                if this.data.delayed.is_empty() {
                    return;
                }
                access.initialize_trie_level(&this.data.delayed, &mut this.data.data);
                this.data.delayed.clear();
            });
            &*self.0.get()
        }
    }

    fn for_each<'a>(&'a self, access: &TrieAccess, mut f: impl FnMut(Value, &'a LazyTrie)) {
        let forced = &self.force(access).data;
        for (k, v) in &forced.data {
            f(*k, v)
        }
    }

    fn get(&self, access: &TrieAccess, value: Value) -> Option<&LazyTrie> {
        let forced = &self.force(access).data;
        forced.data.get(&value)
    }
}

struct TrieAccess<'a> {
    function: &'a Function,
    timestamp_range: Range<u32>,
    column: usize,
    constraints: Vec<Constraint>,
}

impl<'a> std::fmt::Display for TrieAccess<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.function.decl.name, self.column)
    }
}

impl<'a> TrieAccess<'a> {
    #[cold]
    fn initialize_trie_level(&self, idxs: &[RowIdx], map: &mut SparseMap) {
        log::trace!("initializing {idxs:?}");
        let arity = self.function.schema.input.len();
        let mut insert = |i: usize, tup: &[Value], out: Value, val: Value| {
            use hashbrown::hash_map::Entry;
            // self.timestamp_range.contains(&out.timestamp)
            if self.constraints.iter().all(|c| c.check(tup, out)) {
                match map.entry(val) {
                    Entry::Occupied(mut e) => {
                        e.get_mut().0.get_mut().data.delayed.push(i as RowIdx)
                    }
                    Entry::Vacant(e) => {
                        e.insert(LazyTrie(UnsafeCell::new(LazyTrieInner {
                            data: LazyTrieData {
                                delayed: smallvec::smallvec![i as RowIdx],
                                data: Default::default(),
                            },
                        })));
                    }
                }
            }
        };

        if idxs.is_empty() {
            log::trace!(
                "standard initialization, ts_range={:?}",
                self.timestamp_range
            );
            if self.column < arity {
                for FunctionEntry { index, inputs, out } in self
                    .function
                    .iter_timestamp_range(self.timestamp_range.clone())
                {
                    insert(index, inputs, out, inputs[self.column])
                }
            } else {
                assert_eq!(self.column, arity);
                for FunctionEntry { index, inputs, out } in self
                    .function
                    .iter_timestamp_range(self.timestamp_range.clone())
                {
                    insert(index, inputs, out, out)
                }
            }
        } else if self.column < arity {
            for FunctionEntry { index, inputs, out } in self.function.project(idxs) {
                insert(index, inputs, out, inputs[self.column])
            }
        } else {
            assert_eq!(self.column, arity);
            for FunctionEntry { index, inputs, out } in self.function.project(idxs) {
                insert(index, inputs, out, out)
            }
        }
    }
}

fn range_diff(
    cur_range: Range<u32>,
    needed_range: Range<u32>,
) -> (/* diff */ Range<u32>, /* union */ Range<u32>) {
    // We assume 'cur_range' starts at 0, otherwise we could require 2 diffs.
    // That's doable but we are avoiding it for now.
    debug_assert_eq!(cur_range.start, 0);
    (
        cur_range.end..needed_range.end,
        cmp::min(cur_range.start, needed_range.start)..cmp::max(needed_range.end, cur_range.end),
    )
}

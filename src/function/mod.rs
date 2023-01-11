use smallvec::SmallVec;

use crate::{
    proofs::{EqJustification, RowJustification, RowOffset},
    *,
};

pub(crate) use self::table::InsertResult;

mod binary_search;
pub mod index;
mod table;

pub type ValueVec = SmallVec<[Value; 3]>;

#[derive(Clone)]
pub struct Function {
    pub decl: FunctionDecl,
    pub schema: ResolvedSchema,
    pub merge: MergeFn,
    pub(crate) nodes: table::Table,
    sorts: HashSet<Symbol>,
    pub(crate) indexes: Vec<Rc<ColumnIndex>>,
    index_updated_through: usize,
    updates: usize,
    scratch: IndexSet<usize>,
}

#[derive(Clone)]
pub enum MergeFn {
    AssertEq,
    Union,
    // the rc is make sure it's cheaply clonable, since calling the merge fn
    // requires a clone
    Expr(Rc<Program>),
}

#[derive(Debug, Clone)]
pub struct TupleOutput {
    pub value: Value,
    pub timestamp: u32,
    pub reason: RowJustification,
}

#[derive(Clone, Debug)]
pub struct ResolvedSchema {
    pub input: Vec<ArcSort>,
    pub output: ArcSort,
}

impl Function {
    pub fn new(egraph: &EGraph, decl: &FunctionDecl) -> Result<Self, Error> {
        let mut input = Vec::with_capacity(decl.schema.input.len());
        for s in &decl.schema.input {
            input.push(match egraph.sorts.get(s) {
                Some(sort) => sort.clone(),
                None => return Err(Error::TypeError(TypeError::Unbound(*s))),
            })
        }

        let output = match egraph.sorts.get(&decl.schema.output) {
            Some(sort) => sort.clone(),
            None => return Err(Error::TypeError(TypeError::Unbound(decl.schema.output))),
        };

        let merge = if let Some(merge_expr) = &decl.merge {
            let mut types = IndexMap::<Symbol, ArcSort>::default();
            types.insert("old".into(), output.clone());
            types.insert("new".into(), output.clone());
            let (_, program) = egraph
                .compile_expr(&types, merge_expr, Some(output.clone()))
                .map_err(Error::TypeErrors)?;
            MergeFn::Expr(Rc::new(program))
        } else if output.is_eq_sort() {
            MergeFn::Union
        } else {
            MergeFn::AssertEq
        };

        let indexes = Vec::from_iter(
            input
                .iter()
                .chain(once(&output))
                .map(|x| Rc::new(ColumnIndex::new(x.name()))),
        );

        let sorts: HashSet<Symbol> = input
            .iter()
            .map(|x| x.name())
            .chain(once(output.name()))
            .collect();

        Ok(Function {
            decl: decl.clone(),
            schema: ResolvedSchema { input, output },
            nodes: Default::default(),
            scratch: Default::default(),
            sorts,
            // TODO: build indexes for primitive sorts lazily
            indexes,
            index_updated_through: 0,
            updates: 0,
            merge,
            // TODO figure out merge and default here
        })
    }

    pub fn insert(
        &mut self,
        inputs: &[Value],
        value: Value,
        timestamp: u32,
        reason: RowJustification,
    ) -> Option<(Value, InsertResult)> {
        self.insert_internal(inputs, value, timestamp, reason, true)
    }
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.indexes
            .iter_mut()
            .for_each(|x| Rc::make_mut(x).clear());
        self.index_updated_through = 0;
    }
    pub fn insert_internal(
        &mut self,
        inputs: &[Value],
        value: Value,
        timestamp: u32,
        reason: RowJustification,
        // Clean out all stale entries if they account for a sufficiently large
        // portion of the table after this entry is inserted.
        maybe_rehash: bool,
    ) -> Option<(Value, InsertResult)> {
        let res = self.nodes.insert(inputs, value, timestamp, reason);
        if maybe_rehash {
            self.maybe_rehash();
        }
        res
    }

    /// Return a column index that contains (a superset of) the offsets for the
    /// given column. This method can return nothing if the indexes available
    /// contain too many irrelevant offsets.
    pub(crate) fn column_index(
        &self,
        col: usize,
        timestamps: &Range<u32>,
    ) -> Option<Rc<ColumnIndex>> {
        let range = self.nodes.transform_range(timestamps);
        if range.end > self.index_updated_through {
            return None;
        }
        let size = range.end.saturating_sub(range.start);
        // If this represents >12.5% overhead, don't use the index
        if (self.nodes.len() - size) > (size / 8) {
            return None;
        }
        let target = &self.indexes[col];
        Some(target.clone())
    }

    #[allow(unused)]
    pub fn print_offset(&self, off: RowOffset) {
        self.nodes.dump_offset(off, 0)
    }

    pub(crate) fn remove(&mut self, ks: &[Value], ts: u32) -> bool {
        let res = self.nodes.remove(ks, ts);
        self.maybe_rehash();
        res
    }

    fn build_indexes(&mut self, offsets: Range<usize>) {
        for (col, index) in self.indexes.iter_mut().enumerate() {
            let as_mut = Rc::make_mut(index);
            if col == self.schema.input.len() {
                for (slot, _, out) in self.nodes.iter_range(offsets.clone()) {
                    as_mut.add(out.value, slot)
                }
            } else {
                for (slot, inp, _) in self.nodes.iter_range(offsets.clone()) {
                    as_mut.add(inp[col], slot)
                }
            }
        }
    }

    fn update_indexes(&mut self, through: usize) {
        self.build_indexes(self.index_updated_through..through);
        self.index_updated_through = self.index_updated_through.max(through);
    }

    fn maybe_rehash(&mut self) {
        if !self.nodes.too_stale() {
            return;
        }

        for index in &mut self.indexes {
            // Everything works if we don't have a unique copy of the indexes,
            // but we ought to be able to avoid this copy.
            Rc::make_mut(index).clear();
        }
        self.nodes.rehash();
        self.index_updated_through = 0;
        self.update_indexes(self.nodes.len());
    }

    pub(crate) fn iter_timestamp_range(
        &self,
        timestamps: &Range<u32>,
    ) -> impl Iterator<Item = (usize, &[Value], &TupleOutput)> {
        self.nodes.iter_timestamp_range(timestamps)
    }

    pub fn rebuild(&mut self, uf: &mut UnionFind, timestamp: u32) -> usize {
        // Make sure indexes are up to date.
        self.update_indexes(self.nodes.len());
        if self.schema.input.iter().all(|s| !s.is_eq_sort()) && !self.schema.output.is_eq_sort() {
            return std::mem::take(&mut self.updates);
        }
        let mut scratch = ValueVec::new();
        let n_unions = uf.n_unions();
        if uf.new_ids(|sort| self.sorts.contains(&sort)) > (self.nodes.len() / 2) {
            // basic heuristic: if we displaced a large number of ids relative
            // to the size of the table, then just rebuild everything.
            for i in 0..self.nodes.len() {
                self.rebuild_at(i, timestamp, uf, &mut scratch)
            }
        } else {
            let mut to_canon = mem::take(&mut self.scratch);
            to_canon.clear();
            to_canon.extend(self.indexes.iter().flat_map(|x| x.to_canonicalize(uf)));

            for i in to_canon.iter().copied() {
                self.rebuild_at(i, timestamp, uf, &mut scratch);
            }
            self.scratch = to_canon;
        }
        self.maybe_rehash();
        uf.n_unions() - n_unions + std::mem::take(&mut self.updates)
    }

    fn rebuild_at(&mut self, i: usize, timestamp: u32, uf: &mut UnionFind, scratch: &mut ValueVec) {
        let mut modified = false;
        let (args, out) = if let Some(x) = self.nodes.get_index(i) {
            x
        } else {
            // Entry is stale
            return;
        };
        let mut out_val = out.value;
        scratch.clear();
        scratch.extend(args.iter().copied());
        let start = scratch.len();

        for (i, ty) in (0..start).zip(&self.schema.input) {
            let val = scratch[i];
            if !ty.is_eq_sort() {
                scratch.push(val);
                continue;
            }
            let new = uf.find_value(val);
            if new.bits != val.bits {
                modified = true;
            }
            scratch.push(new);
        }

        if self.schema.output.is_eq_sort() {
            let new = uf.find_value(out_val);
            if new.bits != out_val.bits {
                out_val = new;
                modified = true;
            }
        }

        if !modified {
            return;
        }
        self.nodes.remove_index(i, timestamp);
        let new_offset = self
            .nodes
            .insert_and_merge(&scratch[start..], timestamp, |prev| {
                if let Some(prev) = prev {
                    if !self.schema.output.is_eq_sort() {
                        // TODO: call the merge fn
                        return prev;
                    }
                    let mut res = None;
                    for (prev_arg, canon_arg) in
                        scratch[0..start].iter().zip(scratch[start..].iter())
                    {
                        // Add a congruence edge for every re-canonicalized item.
                        if prev_arg.bits != canon_arg.bits {
                            res = Some(uf.union_values(
                                prev,
                                out_val,
                                self.schema.output.name(),
                                EqJustification::Cong(
                                    Id::from(prev_arg.bits as usize),
                                    Id::from(canon_arg.bits as usize),
                                ),
                            ));
                        }
                    }
                    res.unwrap()
                } else {
                    out_val
                }
            });
        match new_offset {
            InsertResult::Merged(merged) => {
                let merged = self.nodes.save(merged);
                let rebuilt = self.nodes.save(i);
                self.nodes.set_reason(
                    self.nodes.len() - 1,
                    RowJustification::Merged { rebuilt, merged },
                );
            }
            InsertResult::Append => {
                let prev = self.nodes.save(i);
                self.nodes
                    .set_reason(self.nodes.len() - 1, RowJustification::Rebuilt(prev));
            }
            InsertResult::NoChange(_) => {
                // Good to go!
            }
        }
    }

    pub(crate) fn get_size(&self, range: &Range<u32>) -> usize {
        self.nodes.approximate_range_size(range)
    }
}

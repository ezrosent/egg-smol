use std::collections::BTreeMap;

use fixedbitset::FixedBitSet;
use smallvec::SmallVec;

use crate::{
    common::{DenseIdMap, HashMap, HashSet, IndexSet, NumericId},
    offsets::Subset,
    pool::Pooled,
    query::{Atom, Query},
    table_spec::Constraint,
};

use super::{ActionId, AtomId, ColumnId, SubAtom, VarInfo, Variable};

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ScanSpec {
    pub to_index: SubAtom,
    // Only yield rows where the given constraints match.
    pub constraints: Vec<Constraint>,
}

#[derive(Debug)]
pub(crate) enum JoinStage {
    EvalConstraints {
        atom: AtomId,
        /// We currently aren't using these at all. The plan is to use this to
        /// dedup plan stages later (it also helps for debugging).
        #[allow(unused)]
        constraints: Pooled<Vec<Constraint>>,
        /// A pre-computed table subset that we can use to filter the table,
        /// given these constaints.
        ///
        /// Why use the constraints at all? Because we want to use them to
        /// discover common plan nodes from different queries (subsets can be
        /// large).
        subset: Subset,
    },
    Intersect {
        cover: ScanSpec,
        bind: SmallVec<[(ColumnId, Variable); 2]>,
        to_intersect: Vec<(ScanSpec, SmallVec<[ColumnId; 4]>)>,
    },
    RunInstrs {
        actions: ActionId,
    },
}

#[derive(Debug)]
pub(crate) struct Plan {
    pub atoms: DenseIdMap<AtomId, Atom>,
    pub stages: Vec<JoinStage>,
}

type VarSet = FixedBitSet;
type AtomSet = FixedBitSet;

/// The algorithm used to produce a free join plan.
#[derive(Default, Copy, Clone)]
pub enum PlanStrategy {
    /// Iteratively pick the smallest atom as the cover for the next stage,
    /// until all subatoms have been visited.
    ///
    /// This is currently unused, but we are keeping this code around because of
    /// the potential for future strategies, as well as to allow for further
    /// evaluation of this strategy later.
    #[allow(unused)]
    PureSize,

    /// Pick an approximate minimal set of covers, then order those covers in
    /// increasing order of size.
    ///
    /// This is similar to PureSize but we first limit the potential atoms that
    /// can act as covers so as to minimize the total number of stages in the
    /// plan. This is only an approximate minimum: the problem of finding the
    /// exact minimum ("set cover") is NP-hard.
    #[default]
    MinCover,
}

pub(crate) fn plan_query(query: Query, strategy: PlanStrategy) -> Plan {
    let mut planner = Planner::new(&query.var_info, &query.atoms);
    let mut res = planner.plan(strategy);
    res.stages.push(JoinStage::RunInstrs {
        actions: query.action,
    });
    res
}

struct Planner<'a> {
    // immutable
    vars: &'a DenseIdMap<Variable, VarInfo>,
    atoms: &'a DenseIdMap<AtomId, Atom>,

    // mutable
    used: VarSet,
    constrained: AtomSet,

    scratch_subatom: HashMap<AtomId, SmallVec<[ColumnId; 4]>>,
}

/// StageInfo is an intermediate stage used to describe the ordering of
/// operations. One of these contains enough information to "expand" it to a
/// JoinStage, but it still contains variable information.
///
/// This separation makes it easier for us to iterate with different planning
/// algorithms while sharing the same "backend" that generates a concrete plan.
struct StageInfo {
    cover: SubAtom,
    vars: Vec<Variable>,
    filters: Vec<(
        SubAtom,                 /* the subatom to index */
        SmallVec<[ColumnId; 4]>, /* how to build a key for that index from the cover atom */
    )>,
}

impl<'a> Planner<'a> {
    pub(crate) fn new(
        vars: &'a DenseIdMap<Variable, VarInfo>,
        atoms: &'a DenseIdMap<AtomId, Atom>,
    ) -> Self {
        Planner {
            vars,
            atoms,
            used: VarSet::with_capacity(vars.n_ids()),
            constrained: AtomSet::with_capacity(atoms.n_ids()),
            scratch_subatom: Default::default(),
        }
    }
    pub(crate) fn plan(&mut self, strat: PlanStrategy) -> Plan {
        let mut stages = Vec::new();
        self.used.clear();
        self.constrained.clear();
        let mut remaining_constraints: DenseIdMap<AtomId, (usize, &Pooled<Vec<Constraint>>)> =
            Default::default();
        // First, plan all the constants:
        for (atom, atom_info) in self.atoms.iter() {
            remaining_constraints.insert(
                atom,
                (
                    atom_info.constraints.approx_size(),
                    &atom_info.constraints.slow,
                ),
            );
            if atom_info.constraints.fast.is_empty() {
                continue;
            }
            stages.push(JoinStage::EvalConstraints {
                atom,
                constraints: Pooled::cloned(&atom_info.constraints.fast),
                subset: atom_info.constraints.subset.clone(),
            });
        }

        let mut size_info = Vec::<(AtomId, usize)>::new();
        match strat {
            PlanStrategy::PureSize => {
                for (atom, (size, _)) in remaining_constraints.iter() {
                    size_info.push((atom, *size));
                }
            }
            PlanStrategy::MinCover => {
                let mut eligible_covers = HashSet::default();
                let mut queue = BucketQueue::new(self.vars, self.atoms);
                while let Some(atom) = queue.pop_min() {
                    eligible_covers.insert(atom);
                }
                for (atom, (size, _)) in remaining_constraints
                    .iter()
                    .filter(|(atom, _)| eligible_covers.contains(atom))
                {
                    size_info.push((atom, *size));
                }
            }
        };
        size_info.sort_unstable_by_key(|(_, size)| *size);
        let mut atoms = size_info.iter().map(|(atom, _)| *atom);
        while let Some(info) = self.get_next(&mut atoms) {
            stages.push(self.compile_stage(info))
        }
        Plan {
            atoms: self.atoms.clone(),
            stages,
        }
    }

    fn get_next(&mut self, ordering: &mut impl Iterator<Item = AtomId>) -> Option<StageInfo> {
        loop {
            let mut covered = false;
            let mut filters = Vec::new();
            let atom = ordering.next()?;
            let atom_info = &self.atoms[atom];
            let mut cover = SubAtom::new(atom);
            let mut vars = Vec::new();
            for (ix, var) in atom_info.column_to_var.iter() {
                if self.used.contains(var.index()) {
                    continue;
                }
                // This atom is not completely covered by previous stages.
                covered = true;
                self.used.insert(var.index());
                vars.push(*var);
                cover.vars.push(ix);
                for subatom in self.vars[*var].occurrences.iter() {
                    if subatom.atom == atom {
                        continue;
                    }
                    self.scratch_subatom
                        .entry(subatom.atom)
                        .or_default()
                        .extend(subatom.vars.iter().copied());
                }
            }
            if !covered {
                // Search the next atom.
                continue;
            }
            for (atom, cols) in self.scratch_subatom.drain() {
                let mut form_key = SmallVec::<[ColumnId; 4]>::new();
                for var_ix in &cols {
                    let var = self.atoms[atom].column_to_var[*var_ix];
                    // form_key is an index _into the subatom forming the cover_.
                    let cover_col = vars
                        .iter()
                        .enumerate()
                        .find(|(_, v)| **v == var)
                        .map(|(ix, _)| ix)
                        .unwrap();
                    form_key.push(ColumnId::from_usize(cover_col));
                }
                filters.push((SubAtom { atom, vars: cols }, form_key));
            }
            return Some(StageInfo {
                cover,
                vars,
                filters,
            });
        }
    }

    fn compile_stage(
        &mut self,
        StageInfo {
            cover,
            vars,
            filters,
        }: StageInfo,
    ) -> JoinStage {
        let atom = cover.atom;
        let cover = ScanSpec {
            to_index: cover,
            constraints: if !self.constrained.put(atom.index()) {
                self.atoms[atom].constraints.slow.clone()
            } else {
                Default::default()
            },
        };
        let mut bind = SmallVec::new();
        let var_set = &self.atoms[atom].var_to_column;
        for var in vars {
            bind.push((var_set[&var], var));
        }

        let mut to_intersect = Vec::with_capacity(filters.len());
        for (subatom, key_spec) in filters {
            let atom = subatom.atom;
            let scan = ScanSpec {
                to_index: subatom,
                constraints: if !self.constrained.put(atom.index()) {
                    self.atoms[atom].constraints.fast.clone()
                } else {
                    Default::default()
                },
            };
            to_intersect.push((scan, key_spec));
        }

        JoinStage::Intersect {
            cover,
            bind,
            to_intersect,
        }
    }
}

/// Datastructure used to greedily solve the set cover problem for a given free
/// join plan.
struct BucketQueue<'a> {
    var_info: &'a DenseIdMap<Variable, VarInfo>,
    cover: VarSet,
    atom_info: DenseIdMap<AtomId, VarSet>,
    sizes: BTreeMap<usize, IndexSet<AtomId>>,
}

impl<'a> BucketQueue<'a> {
    fn new(var_info: &'a DenseIdMap<Variable, VarInfo>, atoms: &DenseIdMap<AtomId, Atom>) -> Self {
        let cover = VarSet::with_capacity(var_info.n_ids());
        let mut atom_info = DenseIdMap::with_capacity(atoms.n_ids());
        let mut sizes = BTreeMap::<usize, IndexSet<AtomId>>::new();
        for (id, atom) in atoms.iter() {
            let mut bitset = VarSet::with_capacity(var_info.n_ids());
            for (_, var) in atom.column_to_var.iter() {
                bitset.insert(var.index());
            }
            sizes.entry(bitset.count_ones(..)).or_default().insert(id);
            atom_info.insert(id, bitset);
        }
        BucketQueue {
            var_info,
            cover,
            atom_info,
            sizes,
        }
    }

    /// Return the atom with the largest number of uncovered variables. A
    /// variable is "covered" if a previous call to `pop_min` returned an atom
    /// referencing that variable.
    fn pop_min(&mut self) -> Option<AtomId> {
        // Pick an arbitrary atom from the smallest bucket.
        let (_, atoms) = self.sizes.iter_mut().next_back()?;
        let res = atoms.pop().unwrap();
        let vars = self.atom_info[res].clone();
        // For each variable that we added to the cover, remove it from the
        // entries in atom_info referencing it and update `sizes` to reflect the
        // new ordering.
        for new_var in vars.difference(&self.cover).map(Variable::from_usize) {
            for subatom in &self.var_info[new_var].occurrences {
                let cur_set = &mut self.atom_info[subatom.atom];
                let old_size = cur_set.count_ones(..);
                cur_set.difference_with(&vars);
                let new_size = cur_set.count_ones(..);
                if old_size == new_size {
                    continue;
                }
                if let Some(old_size_set) = self.sizes.get_mut(&old_size) {
                    old_size_set.remove(&subatom.atom);
                    if old_size_set.is_empty() {
                        self.sizes.remove(&old_size);
                    }
                }
                if new_size > 0 {
                    self.sizes.entry(new_size).or_default().insert(subatom.atom);
                }
            }
        }
        self.cover.union_with(&vars);
        Some(res)
    }
}

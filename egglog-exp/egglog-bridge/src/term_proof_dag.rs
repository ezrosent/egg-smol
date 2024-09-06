use std::{
    collections::{hash_map::Entry, HashMap},
    io::{self, Write},
    rc::Rc,
};

pub enum TermValue<Prf> {
    Prim(String),
    SubTerm(Rc<Prf>),
}

pub enum EqProof {
    /// The (trivial) proof that a row equals itself.
    Id(Rc<TermProof>),
    /// An explanation of the existence of a row in the union-find.
    Base(Rc<TermProof>),
    /// A proof that `x = y` by way of `y = x`.
    Backwards(Rc<EqProof>),
    /// A proof that `x = z` by way of `x = y`, `y = z` (for any number of
    /// intermediate `y`s).
    Trans(Vec<Rc<EqProof>>),
}

pub enum TermProof {
    /// A proof that a term `r'` exists because:
    /// * Another term `r` exists, and
    /// * Each argument in `r` is equal to `r'`.
    Cong {
        func: Rc<str>,
        old_term: Rc<TermProof>,
        new_term: Rc<TermProof>,
        pairwise_eq: Vec<TermValue<EqProof>>,
    },
    /// The base case of a proof. Terms that were added as base values to the
    /// database.
    Fiat {
        desc: Rc<str>,
        func: Rc<str>,
        row: Vec<TermValue<TermProof>>,
    },

    /// Proof that a term exists because it exists as a subterm of another term.
    Proj {
        index: usize,
        subterm: Rc<TermProof>,
    },
    /// A proof of the existence of a term by applying a rule to the databse.
    FromRule {
        rule_desc: Rc<str>,
        atom_desc: Rc<str>,
        func: Rc<str>,
        row: Vec<TermValue<TermProof>>,
        premises: Vec<Rc<TermProof>>,
        premises_eq: Vec<Rc<EqProof>>,
    },
}

impl TermProof {
    pub fn dump_explanation(&self, writer: &mut impl Write) -> io::Result<()> {
        let mut printer = Printer::default();
        printer.print_term(self, "", writer)
    }
}

#[derive(Default)]
struct Printer {
    ids: HashMap<usize, usize>,
}

impl Printer {
    /// Get the id associated with the given pointer, creating a new one if one
    /// does not exist.
    ///
    /// The second value in the tuple is `true` if a new id was created.
    fn get_id<T>(&mut self, node: &T) -> (usize, bool) {
        let len = self.ids.len();
        match self.ids.entry(node as *const T as usize) {
            Entry::Occupied(o) => (*o.get(), false),
            Entry::Vacant(v) => (*v.insert(len), true),
        }
    }

    fn get_term_id(&mut self, term: &TermProof, writer: &mut impl Write) -> io::Result<String> {
        let (id, is_new) = self.get_id(term);
        if is_new {
            self.print_term(term, &format!("let t{id} = "), writer)?;
        }
        Ok(format!("t{id}"))
    }

    fn get_eq_id(&mut self, eq: &EqProof, writer: &mut impl Write) -> io::Result<String> {
        let (id, is_new) = self.get_id(eq);
        if is_new {
            self.print_eq(eq, &format!("let e{id} = "), writer)?;
        }
        Ok(format!("e{id}"))
    }

    fn print_term(
        &mut self,
        term: &TermProof,
        prefix: &str,
        writer: &mut impl Write,
    ) -> io::Result<()> {
        match term {
            TermProof::Cong {
                func,
                old_term,
                new_term,
                pairwise_eq,
            } => {
                let old_term = self.get_term_id(old_term.as_ref(), writer)?;
                let new_term = self.get_term_id(new_term.as_ref(), writer)?;
                let eq_subproofs = DisplayList(
                    try_collect(pairwise_eq.iter().map(|t| match t {
                        TermValue::Prim(s) => Ok(s.clone()),
                        TermValue::SubTerm(subterm) => self.get_eq_id(subterm.as_ref(), writer),
                    }))?,
                    " ",
                );
                writeln!(
                    writer,
                    "{prefix}Cong {{ {old_term} => {new_term} [{func} {eq_subproofs}] }}"
                )?;
            }
            TermProof::Fiat { desc, func, row } => {
                let term = DisplayList(
                    try_collect(row.iter().map(|t| match t {
                        TermValue::Prim(s) => Ok(s.clone()),
                        TermValue::SubTerm(subterm) => self.get_term_id(subterm.as_ref(), writer),
                    }))?,
                    " ",
                );
                writeln!(writer, "{prefix}Fiat {{ {desc}, ({func} {term}) }}")?;
            }
            TermProof::Proj { index, subterm } => {
                let id = self.get_term_id(subterm.as_ref(), writer)?;
                writeln!(writer, "{prefix}Proj {{ {id}[{index}] }}")?;
            }
            TermProof::FromRule {
                rule_desc,
                atom_desc,
                func,
                row,
                premises,
                premises_eq,
            } => {
                let premises = DisplayList(
                    try_collect(
                        premises
                            .iter()
                            .map(|p| self.get_term_id(p.as_ref(), writer)),
                    )?,
                    " ",
                );
                let premises_eq = DisplayList(
                    try_collect(
                        premises_eq
                            .iter()
                            .map(|p| self.get_eq_id(p.as_ref(), writer)),
                    )?,
                    " ",
                );
                let row = DisplayList(
                    try_collect(row.iter().map(|t| match t {
                        TermValue::Prim(s) => Ok(s.clone()),
                        TermValue::SubTerm(subterm) => self.get_term_id(subterm.as_ref(), writer),
                    }))?,
                    " ",
                );
                writeln!(
                    writer,
                    "{prefix}FromRule {{\n\trule: {rule_desc}\n\tatom: {atom_desc}\n\t({func} {row})\n\tpremises: {premises}\n\tpremises_eq: {premises_eq}\n}}"
                )?;
            }
        }
        Ok(())
    }

    fn print_eq(&mut self, eq: &EqProof, prefix: &str, writer: &mut impl Write) -> io::Result<()> {
        match eq {
            EqProof::Id(row) => {
                let id = self.get_term_id(row.as_ref(), writer)?;
                writeln!(writer, "{prefix}Id {{ {id} }}")?;
            }
            EqProof::Base(b) => {
                let id = self.get_term_id(b.as_ref(), writer)?;
                writeln!(writer, "{prefix}Union-from-rule {{ {id} }}")?;
            }
            EqProof::Backwards(b) => {
                let id = self.get_eq_id(b.as_ref(), writer)?;
                writeln!(writer, "{prefix}Backwards {{ {id} }}")?;
            }
            EqProof::Trans(eqs) => {
                let eqs = DisplayList(
                    try_collect(eqs.iter().map(|e| self.get_eq_id(e.as_ref(), writer)))?,
                    " -> ",
                );
                writeln!(writer, "{prefix}Transitivity {{ {eqs} }}")?;
            }
        }
        Ok(())
    }
}

fn try_collect<T, E, I>(iter: I) -> Result<Vec<T>, E>
where
    I: Iterator<Item = Result<T, E>>,
{
    iter.collect()
}

/// A basic helper for display-formatting lists of items.
pub(crate) struct DisplayList<T>(pub Vec<T>, pub &'static str);

impl<T: std::fmt::Display> std::fmt::Display for DisplayList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();
        if let Some(first) = iter.next() {
            write!(f, "{first}")?;
            for item in iter {
                write!(f, "{}{item}", self.1)?;
            }
        }
        Ok(())
    }
}

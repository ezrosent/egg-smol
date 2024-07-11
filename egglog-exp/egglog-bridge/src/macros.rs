use std::collections::HashMap;

use numeric_id::NumericId;

use crate::{ColumnTy, QueryEntry};

use crate::{
    rule::{Function, Variable},
    RuleBuilder,
};

#[macro_export]
#[doc(hidden)]
macro_rules! parse_rhs_atom_args {
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, []) => { };
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [{ $e:expr } $($args:tt)*]) => {
        $v.push($e.into());
        $crate::parse_rhs_atom_args!($ebuilder, $builder, $table, $v, [$($args)*]);
    };
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [$var:ident $($args:tt)*]) => {
        let v = $ebuilder.lookup_var(stringify!($var)).unwrap_or_else(|| {
            panic!("use of unbound variable {} on the right-hand side of a rule", stringify!($var))
        });
        $v.push(v);
        $crate::parse_rhs_atom_args!($ebuilder, $builder, $table, $v, [$($args)*]);
    };
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [($func:tt $($fargs:tt)*) $($args:tt)*]) => {
        let ret = $crate::parse_rhs_atom!($ebuilder, $builder, ($func $($fargs)*));
        $v.push(ret.into());
        $crate::parse_rhs_atom_args!($ebuilder, $builder, $table, $v, [$($args)*]);
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! parse_rhs_atom {
    ($ebuilder:expr, $builder:expr, $var:ident) => {{
        $ebuilder.lookup_var(stringify!($var)).unwrap_or_else(|| {
            panic!("use of unbound variable {} on the right-hand side of a rule", stringify!($var))
        })
    }};
    ($ebuilder:expr, $builder:expr, ($func:tt $($args:tt)*)) => {{
        #[allow(clippy::vec_init_then_push)]
        {
            let mut vec = Vec::<$crate::QueryEntry>::new();
            $crate::parse_rhs_atom_args!($ebuilder, $builder, $func, vec, [$($args)*]);
            $builder.lookup($func.into(), &vec)
        }
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! parse_rhs_command {
    ($ebuilder:expr, $builder:expr, []) => { };
    ($ebuilder:expr, $builder:expr, [(let $i:ident $($expr:tt)*) $($rest:tt)*]) => {
        let res = $crate::parse_rhs_atom!($ebuilder, $builder, $($expr)*);
        $ebuilder.bind_var(stringify!($i), res);
        $crate::parse_rhs_command!($ebuilder, $builder, [$($rest)*]);
    };
    ($ebuilder:expr, $builder:expr, [(set ($func:tt $($args:tt)*) $res:tt) $($rest:tt)*]) => {
        let mut vec = Vec::<$crate::QueryEntry>::new();
        $crate::parse_rhs_atom_args!($ebuilder, $builder, $func, vec, [$($args)*]);
        $crate::parse_rhs_atom_args!($ebuilder, $builder, $func, vec, [$res]);
        $builder.set($func.into(), &vec);
        $crate::parse_rhs_command!($ebuilder, $builder, [$($rest)*]);
    };
    ($ebuilder:expr, $builder:expr, [(union $l:tt $r:tt) $($rest:tt)*]) => {
        let lqe = $crate::parse_rhs_atom!($ebuilder, $builder, $l);
        let rqe = $crate::parse_rhs_atom!($ebuilder, $builder, $r);
        $builder.union(lqe.into(), rqe.into());
        $crate::parse_rhs_command!($ebuilder, $builder, [$($rest)*]);
    };
}

// left-hand side parsing

#[macro_export]
#[doc(hidden)]
macro_rules! parse_lhs_atom_args {
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, []) => {};
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [{ $e:expr } $( $args:tt)*]) => {
        $v.push($e.into());
        $crate::parse_lhs_atom_args!($ebuilder, $builder, $table, $v, [$($args),*]);
    };
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [$var:ident $( $args:tt)*]) => {
        let ret = $ebuilder.get_var(stringify!($var), $table, $v.len(), &mut $builder);
        $v.push(ret.into());
        $crate::parse_lhs_atom_args!($ebuilder, $builder, $table, $v, [$($args),*]);
    };
    ($ebuilder:expr, $builder:expr, $table:ident, $v:expr, [($func:tt $($fargs:tt)*) $($args:tt)*]) => {
        let ret = $crate::parse_lhs_atom!($ebuilder, $builder, ($func $($fargs)*));
        $v.push(ret.into());
        $crate::parse_lhs_atom_args!($ebuilder, $builder, $table, $v, [$($args),*]);
    };
}
#[macro_export]
#[doc(hidden)]
macro_rules! parse_lhs_atom {
    ($ebuilder:expr, $builder:expr; $inferred_ty:expr, $var:ident) => {
        $ebuilder.bind_or_lookup_var(stringify!($var), $inferred_ty, &mut $builder)
    };
    ($ebuilder:expr, $builder:expr; $inferred_ty:expr, ($func:tt $($args:tt)*)) => {
        parse_lhs_atom!($ebuilder, $builder, ($func $($args)*))
    };
    ($ebuilder:expr, $builder:expr, ($func:tt $($args:tt)*)) => {{
        let mut vec = Vec::<$crate::QueryEntry>::new();
        $crate::parse_lhs_atom_args!($ebuilder, $builder, $func, vec, [$($args)*]);
        // Now return the last argument
        let ty = $ebuilder.infer_type($func.into(), vec.len(), &$builder);
        let res = $builder.new_var_named(ty, stringify!($func ($($args)*)));
        vec.push(res.clone());
        $builder.add_atom($func.into(), &vec).unwrap();
        res
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! parse_lhs_atom_with_ret {
    ($ebuilder:expr, $builder:expr, $ret:expr, ($func:tt $($args:tt)*)) => {{
        #[allow(clippy::vec_init_then_push)]
        {
            let mut vec = Vec::<$crate::QueryEntry>::new();
            $crate::parse_lhs_atom_args!($ebuilder, $builder, $func, vec, [$($args)*]);
            vec.push($ret.into());
            $builder.add_atom($func.into(), &vec).unwrap();
        }
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! parse_lhs {
    ($ebuilder:expr, $builder:expr, [$((-> ($func:tt $($args:tt)*) $ret:tt))*]) => {
        $(
            // First, parse the return value, getting a variable out:
            let ty = $ebuilder.infer_return_type($func.into(), &$builder);
            let ret_var = $crate::parse_lhs_atom!($ebuilder, $builder; ty, $ret);
            $crate::parse_lhs_atom_with_ret!($ebuilder, $builder, ret_var, ($func $($args)*));
        )*
    };
}

#[macro_export]
macro_rules! define_rule {
    ([$egraph:expr] ($($lhs:tt)*) => ($($rhs:tt)*))  => {{
        let mut ebuilder = $crate::macros::ExpressionBuilder::default();
        let mut builder = $egraph.new_query_described(stringify!(($($lhs)* => $($rhs)*)));
        $crate::parse_lhs!(ebuilder, builder, [ $($lhs)* ]);
        $crate::parse_rhs_command!(ebuilder, builder, [ $($rhs)* ]);
        builder.build_described(stringify!(($($lhs)* => $($rhs)*)))
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! add_expression {
    ($egraph:expr, $accum:expr, $x:ident) => { $x };
    ($egraph:expr, $accum:expr, ($func:tt $($args:tt)*)) => {{
        let id = $egraph.fresh_id();
        #[allow(unused_mut)]
        {
            let outer = &mut $accum;
            let mut inner = Vec::new();
            outer.push(($func.into(), vec![ $( $crate::add_expression!($egraph, inner, $args),)* id ]));
            outer.extend(inner.into_iter());
        }
        id
    }}
}

#[macro_export]
#[doc(hidden)]
macro_rules! add_expressions_impl {
    ([$egraph:expr, $accum:expr] $($expr:tt)*) => {
        $( $crate::add_expression!($egraph, $accum, $expr); )*
    };
}

#[macro_export]
macro_rules! add_expressions {
    ([$egraph:expr] $($expr:tt)*) => {{
        let mut accum = Vec::new();
        $crate::add_expressions_impl!([$egraph, accum] $($expr)*);
        $egraph.add_values(accum);
    }};
}

/// A struct used specifically to make macro invocations easier to parse. Prefer
/// using [`RuleBuilder`] for constructing rules directly.
///
/// [`RuleBuilder`]: crate::RuleBuilder
#[doc(hidden)]
#[derive(Default)]
pub struct ExpressionBuilder {
    vars: HashMap<&'static str, QueryEntry>,
}

impl ExpressionBuilder {
    pub fn bind_var(&mut self, name: &'static str, var: Variable) {
        if self.vars.contains_key(name) {
            return;
        }
        self.vars.insert(
            name,
            QueryEntry::Var {
                id: var,
                name: Some(name.into()),
            },
        );
    }
    pub fn bind_or_lookup_var(
        &mut self,
        name: &'static str,
        ty: ColumnTy,
        builder: &mut RuleBuilder,
    ) -> QueryEntry {
        if let Some(var) = self.vars.get(name) {
            return var.clone();
        }
        let var = builder.new_var_named(ty, name);
        self.vars.insert(name, var.clone());
        var
    }
    pub fn lookup_var(&mut self, name: &'static str) -> Option<QueryEntry> {
        self.vars.get(name).cloned()
    }

    pub fn get_var(
        &mut self,
        name: &'static str,
        func: impl Into<Function>,
        col: usize,
        rb: &mut RuleBuilder,
    ) -> QueryEntry {
        if let Some(var) = self.vars.get(name) {
            return var.clone();
        }
        let func: Function = func.into();
        let ty = self.infer_type(func, col, rb);
        let var = rb.new_var_named(ty, name);
        self.vars.insert(name, var.clone());
        var
    }

    pub fn infer_return_type(&self, func: Function, rb: &RuleBuilder) -> ColumnTy {
        let egraph = rb.egraph();
        match func {
            Function::Table(t) => {
                let table_info = &egraph.funcs[t];
                table_info.ret_ty()
            }
            Function::Prim(p) => {
                let schema = egraph.db.primitives().get_schema(p);
                ColumnTy::Primitive(schema.ret)
            }
        }
    }

    pub fn infer_type(&self, func: Function, col: usize, rb: &RuleBuilder) -> ColumnTy {
        let egraph = rb.egraph();
        match func {
            Function::Table(t) => {
                let info = &egraph.funcs[t];
                info.schema[col]
            }
            Function::Prim(p) => {
                let schema = egraph.db.primitives().get_schema(p);
                ColumnTy::Primitive(if col.index() == schema.args.len() {
                    schema.ret
                } else {
                    *schema.args.get(col.index()).unwrap_or_else(|| {
                        panic!("Column index out of bounds for primitive function: attempted to access {col:?} but the function only has {} arguments (and one return value)", schema.args.len())
                })
                })
            }
        }
    }
}

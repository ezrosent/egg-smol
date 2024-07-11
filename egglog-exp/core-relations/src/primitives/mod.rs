//! Mechanisms for declaring primitive types and operations on them.

// NB: We use standard Rust dynamic dispatch throughout. If we notice overhead
// resulting from this, we can "vectorize" this API to amortize the cost of
// dynamic type checks across larger batches of invocations.

use std::{
    any::{Any, TypeId},
    fmt::{self, Debug},
    hash::Hash,
};

use numeric_id::{define_id, DenseIdMap};

use crate::{
    action::{
        mask::{Mask, MaskIter, ValueSource},
        Bindings,
    },
    common::{InternTable, Value},
    pool::Pool,
    QueryEntry, Variable,
};

#[cfg(test)]
mod tests;

define_id!(pub PrimitiveId, u32, "an identifier for primitive types");
define_id!(pub PrimitiveFunctionId, u32, "an identifier for primitive operations");

pub trait Primitive: Clone + Hash + Eq + Any + Debug {
    fn intern(&self, table: &mut InternTable<Self, Value>) -> Value {
        table.intern(self)
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl<T: Clone + Hash + Eq + Any + Debug> Primitive for T {}

/// A wrapper used to print a primitive value.
///
/// The given primitive must be registered with the `Primitives` instance,
/// otherwise attempting to call the [`Debug`] implementation will panic.
pub struct PrimitivePrinter<'a> {
    pub prim: &'a Primitives,
    pub ty: PrimitiveId,
    pub val: Value,
}

impl Debug for PrimitivePrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.prim.tables[self.ty].print_value(self.val, f)
    }
}

/// A registry for primitive values and operations on them.
#[derive(Default)]
pub struct Primitives {
    type_ids: InternTable<TypeId, PrimitiveId>,
    tables: DenseIdMap<PrimitiveId, Box<dyn DynamicInternTable>>,
    operations: DenseIdMap<PrimitiveFunctionId, DynamicPrimitveOperation>,
}

impl Primitives {
    /// Get the [`PrimitiveId`] for the given primitive type `P`.
    pub fn get_ty<P: Primitive>(&mut self) -> PrimitiveId {
        self.type_ids.intern(&TypeId::of::<P>())
    }

    /// Get a [`Value`] representing the given primitive `p`.
    pub fn get<P: Primitive>(&mut self, p: P) -> Value {
        let id = self.get_ty::<P>();
        let table = self
            .tables
            .get_or_insert(id, || Box::<InternTable<P, Value>>::default())
            .as_any_mut()
            .downcast_mut::<InternTable<P, Value>>()
            .unwrap();
        p.intern(table)
    }

    /// Get a reference to the primitive value represented by the given [`Value`].
    pub fn unwrap<P: Primitive>(&mut self, v: Value) -> &P {
        let id = self.get_ty::<P>();
        let table = self
            .tables
            .get(id)
            .unwrap()
            .as_any()
            .downcast_ref::<InternTable<P, Value>>()
            .unwrap();
        table.get(v)
    }

    pub fn register_op(&mut self, op: impl PrimitiveOperation + 'static) -> PrimitiveFunctionId {
        self.operations.push(DynamicPrimitveOperation::new(op))
    }

    pub fn get_schema(&self, id: PrimitiveFunctionId) -> PrimitiveFunctionSignature {
        self.operations[id].op.signature()
    }

    #[cfg(test)]
    pub(crate) fn apply_op(&mut self, id: PrimitiveFunctionId, args: &[Value]) -> Option<Value> {
        let mut dyn_op = self.operations.take(id);
        let res = dyn_op.op.apply(self, args);
        self.operations.insert(id, dyn_op);
        res
    }
    pub(crate) fn apply_vectorized(
        &mut self,
        id: PrimitiveFunctionId,
        pool: Pool<Vec<Value>>,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        out_var: Variable,
    ) {
        let mut dyn_op = self.operations.take(id);
        dyn_op
            .op
            .apply_vectorized(self, pool, mask, bindings, args, out_var);
        self.operations.insert(id, dyn_op);
    }
}

struct DynamicPrimitveOperation {
    op: Box<dyn PrimitiveOperationExt>,
}

impl DynamicPrimitveOperation {
    fn new(op: impl PrimitiveOperation + 'static) -> Self {
        Self { op: Box::new(op) }
    }
}

trait DynamicInternTable: Any {
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn print_value(&self, val: Value, f: &mut fmt::Formatter) -> fmt::Result;
}

impl<P: Primitive> DynamicInternTable for InternTable<P, Value> {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn print_value(&self, val: Value, f: &mut fmt::Formatter) -> fmt::Result {
        let p = self.get(val);
        write!(f, "{p:?}")
    }
}

/// The type signature for a primitive function.
pub struct PrimitiveFunctionSignature<'a> {
    pub args: &'a [PrimitiveId],
    pub ret: PrimitiveId,
}

/// A primitive operation on a set of primitive types.
///
/// Most of the time you can get away with using the `lift_operation` macro,
/// which implements this under the hood.
pub trait PrimitiveOperation {
    fn signature(&self) -> PrimitiveFunctionSignature;
    fn apply(&mut self, prims: &mut Primitives, args: &[Value]) -> Option<Value>;
}

pub(crate) trait PrimitiveOperationExt: PrimitiveOperation {
    fn apply_vectorized(
        &mut self,
        prims: &mut Primitives,
        pool: Pool<Vec<Value>>,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        out_var: Variable,
    ) {
        let mut out = pool.get();
        mask.iter_dynamic(
            pool,
            args.iter().map(|v| match v {
                QueryEntry::Var(v) => ValueSource::Slice(&bindings[*v]),
                QueryEntry::Const(c) => ValueSource::Const(*c),
            }),
        )
        .fill_vec(&mut out, Value::stale, |_, args| self.apply(prims, &args));
        bindings.insert(out_var, out);
    }
}

impl<T: PrimitiveOperation> PrimitiveOperationExt for T {}

#[macro_export]
macro_rules! lift_operation_impl {
    ([$arity:expr, $table:expr] fn $name:ident ( $($id:ident : $ty:ty : $n:tt),* ) -> $ret:ty { $body:expr }) => {
         {
            use $crate::primitives::{Primitives, PrimitiveOperation, PrimitiveId, PrimitiveFunctionSignature};
            use $crate::common::Value;
            fn $name(prims: &mut Primitives) -> $crate::primitives::PrimitiveFunctionId {
                struct Impl<F> {
                    arg_prims: Vec<PrimitiveId>,
                    ret: PrimitiveId,
                    f: F,
                }

                impl<F: FnMut($($ty),*) -> $ret> Impl<F> {
                    fn new(f: F, prims: &mut Primitives) -> Self {
                        Self {
                            arg_prims: vec![$(prims.get_ty::<$ty>()),*],
                            ret: prims.get_ty::<$ret>(),
                            f,
                        }
                    }
                }

                impl<F: FnMut($($ty),*) -> $ret> PrimitiveOperation for Impl<F> {
                    fn signature(&self) -> PrimitiveFunctionSignature {
                        PrimitiveFunctionSignature {
                            args: &self.arg_prims,
                            ret: self.ret,
                        }
                    }

                    fn apply(&mut self, prims: &mut Primitives, args: &[Value]) -> Option<Value> {
                        assert_eq!(args.len(), $arity, "wrong number of arguments to {}", stringify!($name));
                        let ret = (self.f)($(prims.unwrap::<$ty>(args[$n]).clone()),*);
                        Some(prims.get(ret))
                    }
                }

                fn __impl($($id: $ty),*) -> $ret {
                    $body
                }

                let op = Impl::new(__impl, prims);
                prims.register_op(op)
            }
            $name($table)
        }
    };
}

#[macro_export]
macro_rules! lift_operation_count {
    ([$next:expr, $table:expr] [$($x:ident : $ty:ty : $n: expr),*] fn $name:ident() -> $ret:ty { $body:expr }) => {
        $crate::lift_operation_impl!(
            [$next, $table] fn $name($($x : $ty : $n),*) -> $ret {
                $body
            }
        )
    };
    ([$next:expr, $table:expr] [$($p:ident : $ty:ty : $n:expr),*] fn $name:ident($id:ident : $hd:ty $(,$rest:ident : $tl:ty)*) -> $ret:ty { $body:expr }) => {
        $crate::lift_operation_count!(
            [($next + 1), $table]
            [$($p : $ty : $n,)* $id : $hd : $next]
            fn $name($($rest:$tl),*) -> $ret {
                $body
            }
        )
    };
}

/// Lifts a function into a primitive operation, adding it to the supplied table
/// of primitives.
#[macro_export]
macro_rules! lift_operation {
    ([$table:expr] fn $name:ident ( $($id:ident : $ty:ty),* ) -> $ret:ty { $($body:tt)* } ) => {
        $crate::lift_operation_count!(
            [0, $table]
            []
            fn $name($($id : $ty),*) -> $ret {{
                $($body)*
            }}
        )
    };
}

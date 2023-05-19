use crate::define_id;

define_id!(pub PrimitiveId, u32);
define_id!(pub FunctionId, u32);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ColumnTy {
    Id,
    Primitive(PrimitiveId),
}

pub struct Schema {
    args: Vec<ColumnTy>,
    ret: ColumnTy,
}

impl Schema {
    pub fn new(cols: impl IntoIterator<Item = ColumnTy>, ret: ColumnTy) -> Schema {
        Schema {
            args: cols.into_iter().collect(),
            ret,
        }
    }

    pub(crate) fn args(&self) -> &[ColumnTy] {
        &self.args
    }

    pub(crate) fn ret(&self) -> &ColumnTy {
        &self.ret
    }

    pub(crate) fn arity(&self) -> usize {
        self.args.len()
    }
}

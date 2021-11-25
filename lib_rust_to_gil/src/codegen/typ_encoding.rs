use crate::prelude::*;
use rustc_middle::ty::{IntTy, UintTy};

impl<'tcx> GilCtxt<'tcx> {
    pub fn encode_type(&self, ty: Ty) -> Literal {
        use TyKind::*;
        if ty.is_unit() {
            return Literal::String("()".to_string());
        };
        match &ty.kind() {
            Never => fatal!(self, "Should not encode never for memory"),
            Bool => "bool".into(),
            Char => "char".into(),
            Int(IntTy::Isize) => "isize".into(),
            Int(IntTy::I8) => "i8".into(),
            Int(IntTy::I16) => "i16".into(),
            Int(IntTy::I32) => "i32".into(),
            Int(IntTy::I64) => "i64".into(),
            Int(IntTy::I128) => "i128".into(),
            Uint(UintTy::Usize) => "usize".into(),
            Uint(UintTy::U8) => "u8".into(),
            Uint(UintTy::U16) => "u16".into(),
            Uint(UintTy::U32) => "u32".into(),
            Uint(UintTy::U64) => "u64".into(),
            Uint(UintTy::U128) => "u128".into(),
            Tuple(_) => ty
                .tuple_fields()
                .map(|x| self.encode_type(x))
                .collect::<Vec<_>>()
                .into(),
            _ => fatal!(self, "Cannot encode this type yet: {:#?}", ty),
        }
    }
}

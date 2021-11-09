use crate::prelude::*;
use rustc_middle::ty::{IntTy, UintTy};

// pub enum TypeValEncoding {
//     Nothing,
//     Val,
//     List(Vec<TypeValEncoding>),
// }
//
// impl TypeValEncoding {
// Produces a literal corresponding to the uninitialized value of this type
// pub fn to_uninitialized(&self) -> Literal {
//     match self {
//         Self::Nothing => Literal::Nono,
//         Self::Val => Literal::Undefined,
//         Self::List(vec) => {
//             let content = vec.iter().map(|y| y.to_uninitialized()).collect();
//             Literal::LList(content)
//         }
//     }
// }
// }

impl<'tcx> GilCtxt<'tcx> {
    pub fn encode_type(&self, ty: Ty) -> Literal {
        use TyKind::*;
        if ty.is_unit() {
            return Literal::String("()".to_string());
        };
        let str = match &ty.kind() {
            Never => fatal!(self, "Should not encode never for memory"),
            Bool => "bool",
            Char => "char",
            Int(IntTy::Isize) => "isize",
            Int(IntTy::I8) => "i8",
            Int(IntTy::I16) => "i16",
            Int(IntTy::I32) => "i32",
            Int(IntTy::I64) => "i64",
            Int(IntTy::I128) => "i128",
            Uint(UintTy::Usize) => "usize",
            Uint(UintTy::U8) => "u8",
            Uint(UintTy::U16) => "u16",
            Uint(UintTy::U32) => "u32",
            Uint(UintTy::U64) => "u64",
            Uint(UintTy::U128) => "u128",
            _ => fatal!(self, "Cannot encode this type yet: {:#?}", ty),
        };
        Literal::String(str.to_string())
    }
}

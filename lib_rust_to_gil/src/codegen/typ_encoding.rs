use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{AdtDef, Const, ConstKind, IntTy, UintTy};

/// This type is use to type-check that we're indeed using a
/// literal obtained from encoding a type
#[derive(Clone, Debug)]
pub struct EncodedType(Literal);

impl From<EncodedType> for Literal {
    fn from(e: EncodedType) -> Self {
        e.0
    }
}

impl From<EncodedType> for Expr {
    fn from(e: EncodedType) -> Self {
        Expr::Lit(e.0)
    }
}

impl From<&str> for EncodedType {
    fn from(s: &str) -> Self {
        Self(s.into())
    }
}

pub trait TypeEncoder<'tcx> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>);
    fn atd_def_name(&self, def: &AdtDef) -> String;

    fn array_size_value(&self, sz: &Const) -> i128 {
        match sz {
            Const {
                val: ConstKind::Value(ConstValue::Scalar(Scalar::Int(x))),
                ..
            } => x.to_bits(x.size()).unwrap() as i128,
            _ => panic!("Invalid array size"),
        }
    }

    fn encode_type(&mut self, ty: Ty<'tcx>) -> EncodedType {
        use TyKind::*;
        match &ty.kind() {
            Never => panic!("Should not encode never for memory"),
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
            // (i32, i32) -> ["tuple", ["i32", "i32"]]
            Tuple(_) => EncodedType(Literal::LList(vec![
                "tuple".into(),
                ty.tuple_fields()
                    .map(|x| self.encode_type(x).into())
                    .collect::<Vec<_>>()
                    .into(),
            ])),
            // &mut t -> ["ref", true, encode(t)]
            Ref(_, ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                EncodedType(Literal::LList(vec![
                    "ref".into(),
                    mutability.into(),
                    self.encode_type(ty).into(),
                ]))
            }
            Adt(def, _) => {
                let name = self.atd_def_name(def);
                // Adts are encoded by the environment
                self.add_type_to_genv(ty);
                EncodedType(Literal::LList(vec!["named".into(), name.into()]))
            }
            Slice(ty) => EncodedType(Literal::LList(vec![
                "slice".into(),
                self.encode_type(ty).into(),
            ])),
            Array(ty, sz) => {
                let sz_i = self.array_size_value(sz);
                EncodedType(
                    vec![
                        "array".into(),
                        self.encode_type(ty).into(),
                        Literal::Int(sz_i),
                    ]
                    .into(),
                )
            }
            _ => panic!("Cannot encode this type yet: {:#?}", ty),
        }
    }
}

impl<'tcx, 'body> TypeEncoder<'tcx> for GilCtxt<'tcx, 'body> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>) {
        self.global_env.add_type(ty);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.ty_ctxt.item_name(def.did).to_string()
    }
}

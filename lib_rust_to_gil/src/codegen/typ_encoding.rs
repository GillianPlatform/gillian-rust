use crate::prelude::*;
use rustc_middle::ty::{AdtDef, IntTy, UintTy};

pub trait TypeEncoderable<'tcx> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>);
    fn atd_def_name(&self, def: &AdtDef) -> String;
}

pub trait TypeEncoder<'tcx> {
    fn encode_type(&mut self, ty: Ty<'tcx>) -> Literal;
}

impl<'tcx, T> TypeEncoder<'tcx> for T
where
    T: TypeEncoderable<'tcx>,
{
    fn encode_type(&mut self, ty: Ty<'tcx>) -> Literal {
        use TyKind::*;
        if ty.is_unit() {
            return Literal::String("()".to_string());
        };
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
            Tuple(_) => Literal::LList(vec![
                "tuple".into(),
                ty.tuple_fields()
                    .map(|x| self.encode_type(x))
                    .collect::<Vec<_>>()
                    .into(),
            ]),
            // &mut t -> ["ref", true, encode(t)]
            Ref(_, ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                Literal::LList(vec!["ref".into(), mutability.into(), self.encode_type(ty)])
            }
            Adt(def, _) if def.is_struct() => {
                let name = self.atd_def_name(def);
                self.add_type_to_genv(ty);
                Literal::LList(vec!["struct".into(), name.into()])
            }
            _ => panic!("Cannot encode this type yet: {:#?}", ty),
        }
    }
}

impl<'tcx, 'body> TypeEncoderable<'tcx> for GilCtxt<'tcx, 'body> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>) {
        self.global_env.add_type(ty);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.ty_ctxt.item_name(def.did).to_string()
    }
}

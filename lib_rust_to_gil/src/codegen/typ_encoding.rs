use crate::prelude::*;
use rustc_middle::ty::{
    AdtDef, AliasTy, Const, ConstKind, GenericArg, GenericArgKind, ParamTy, Region,
};
use rustc_type_ir::{AliasKind, IntTy, UintTy};
use serde_json::json;

/// This type is use to type-check that we're indeed using a
/// literal obtained from encoding a type
#[derive(Clone, Debug)]
pub struct EncodedType(Expr);

impl From<EncodedType> for Expr {
    fn from(e: EncodedType) -> Self {
        e.0
    }
}

impl From<&str> for EncodedType {
    fn from(s: &str) -> Self {
        Self(s.into())
    }
}

pub fn type_param_name(index: u32, name: Symbol) -> String {
    format!("pty_{}{}", name, index)
}

pub fn lifetime_param_name(name: &str) -> String {
    format!("pLft_{}", name)
}

pub fn region_name(reg: Region) -> String {
    // Drop the '
    if let Some(nm) = reg.get_name() {
        lifetime_param_name(&nm.as_str()[1..])
    } else if reg.is_var() {
        lifetime_param_name(&reg.as_var().as_u32().to_string())
    } else {
        lifetime_param_name("anon")
    }
}

pub fn encode_sym_array(ty: EncodedType, length: Expr) -> EncodedType {
    EncodedType([Expr::from("array"), ty.into(), length].into())
}
pub trait TypeEncoder<'tcx>: crate::utils::tcx_utils::HasTyCtxt<'tcx> + HasGlobalEnv<'tcx> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.global_env_mut().register_adt(def);
    }

    fn adt_def_name(&self, def: &AdtDef) -> String {
        self.tcx().item_name(def.did()).to_string()
    }

    fn array_size_value(&self, sz: &Const) -> i128 {
        match sz.kind() {
            ConstKind::Value(ValTree::Leaf(x)) => x.try_to_bits(x.size()).unwrap() as i128,
            _ => panic!("Invalid array size"),
        }
    }

    fn serialize_generic_arg(&mut self, arg: GenericArg<'tcx>) -> Option<serde_json::Value> {
        match arg.unpack() {
            // We don't make use of Lifetime arguments for now
            GenericArgKind::Lifetime(..) => None,
            GenericArgKind::Const(..) => None,
            GenericArgKind::Type(ty) => Some(self.serialize_type(ty)),
        }
    }

    fn serialize_type(&mut self, ty: Ty<'tcx>) -> serde_json::Value {
        // This is mostly duplicated from encode_type, it should be factorize
        // together under serde, with 2 different serializers or something.
        use rustc_middle::ty::*;

        fn serialize_scalar(name: &str) -> serde_json::Value {
            json!(["Scalar", name])
        }

        match ty.kind() {
            Never => panic!("Should not encode never for tyenv"),
            Bool => serialize_scalar("bool"),
            Char => serialize_scalar("char"),
            Int(IntTy::Isize) => serialize_scalar("isize"),
            Int(IntTy::I8) => serialize_scalar("i8"),
            Int(IntTy::I16) => serialize_scalar("i16"),
            Int(IntTy::I32) => serialize_scalar("i32"),
            Int(IntTy::I64) => serialize_scalar("i64"),
            Int(IntTy::I128) => serialize_scalar("i128"),
            Uint(UintTy::Usize) => serialize_scalar("usize"),
            Uint(UintTy::U8) => serialize_scalar("u8"),
            Uint(UintTy::U16) => serialize_scalar("u16"),
            Uint(UintTy::U32) => serialize_scalar("u32"),
            Uint(UintTy::U64) => serialize_scalar("u64"),
            Uint(UintTy::U128) => serialize_scalar("u128"),
            Tuple(_) => json!([
                "Tuple",
                ty.tuple_fields()
                    .iter()
                    .map(|x| self.serialize_type(x))
                    .collect::<Vec<_>>()
            ]),
            RawPtr(ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                json!([ "Ptr", {
                    "mut": mutability,
                    "ty": self.serialize_type(*ty)
                }])
            }
            Ref(_, ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                json!([ "Ref", {
                    "mut": mutability,
                    "ty": self.serialize_type(*ty)
                }])
            }
            Adt(def, subst) => {
                let name = self.adt_def_name(def);
                let subst: serde_json::Value = subst
                    .iter()
                    .filter_map(|x| self.serialize_generic_arg(x))
                    .collect();
                // Adts are encoded by the environment
                self.add_adt_to_genv(*def);
                json!(["Adt", [name, subst]])
            }
            Slice(ty) => json!(["Slice", self.serialize_type(*ty)]),
            Array(ty, sz) => {
                let sz_i: i64 = self
                    .array_size_value(sz)
                    .try_into()
                    .expect("Size of array is greater than i64::MAX, cannot encode!");
                json!(["Array", {
                    "length": sz_i,
                    "ty": self.serialize_type(*ty)
                }])
            }
            Param(ParamTy { index, name: _ }) => json!(["Param", index]),
            _ => fatal!(
                self,
                "Cannot serialize this type to json yet: {:?}",
                ty.kind()
            ),
        }
    }

    fn encode_generic_arg(&mut self, arg: GenericArg<'tcx>) -> Option<EncodedType> {
        match arg.unpack() {
            // We don't make use of Lifetime arguments for now
            GenericArgKind::Lifetime(..) => None,
            GenericArgKind::Const(..) => None,
            GenericArgKind::Type(ty) => Some(self.encode_type(ty)),
        }
    }

    fn encode_array_type(&mut self, ty: Ty<'tcx>, size: Expr) -> EncodedType {
        EncodedType([Expr::from("array"), self.encode_type(ty).into(), size].into())
    }

    fn encode_type(&mut self, ty: Ty<'tcx>) -> EncodedType {
        match ty.kind() {
            TyKind::Never => panic!("Should not encode never for memory"),
            TyKind::Bool => "bool".into(),
            TyKind::Char => "char".into(),
            TyKind::Int(IntTy::Isize) => "isize".into(),
            TyKind::Int(IntTy::I8) => "i8".into(),
            TyKind::Int(IntTy::I16) => "i16".into(),
            TyKind::Int(IntTy::I32) => "i32".into(),
            TyKind::Int(IntTy::I64) => "i64".into(),
            TyKind::Int(IntTy::I128) => "i128".into(),
            TyKind::Uint(UintTy::Usize) => "usize".into(),
            TyKind::Uint(UintTy::U8) => "u8".into(),
            TyKind::Uint(UintTy::U16) => "u16".into(),
            TyKind::Uint(UintTy::U32) => "u32".into(),
            TyKind::Uint(UintTy::U64) => "u64".into(),
            TyKind::Uint(UintTy::U128) => "u128".into(),
            TyKind::Str => "str".into(),
            // (i32, i32) -> ["tuple", ["i32", "i32"]]
            TyKind::Tuple(_) => EncodedType(
                [
                    Expr::from("tuple"),
                    ty.tuple_fields()
                        .iter()
                        .map(|x| self.encode_type(x).into())
                        .collect::<Vec<_>>()
                        .into(),
                ]
                .into(),
            ),
            //   *mut t | &mut t -> ["ref", true, encode(t)]
            // We'll have to change this later when we start
            // caring about the aliasing model,
            // but we don't at the moment
            TyKind::RawPtr(ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                EncodedType(
                    [
                        Expr::from("ptr"),
                        mutability.into(),
                        self.encode_type(*ty).into(),
                    ]
                    .into(),
                )
            }
            TyKind::Ref(_, ty, mutability) => {
                let mutability = match mutability {
                    Mutability::Mut => true,
                    Mutability::Not => false,
                };
                EncodedType(
                    [
                        Expr::from("ref"),
                        mutability.into(),
                        self.encode_type(*ty).into(),
                    ]
                    .into(),
                )
            }
            TyKind::Adt(def, subst) => {
                let name = self.adt_def_name(def);
                let args: Vec<_> = subst
                    .iter()
                    .filter_map(|a| self.encode_generic_arg(a))
                    .map(|a| a.0)
                    .collect();
                // Adts are encoded by the environment
                self.add_adt_to_genv(*def);
                EncodedType([Expr::from("adt"), name.into(), args.into()].into())
            }
            TyKind::Slice(ty) => {
                EncodedType([Expr::from("slice"), self.encode_type(*ty).into()].into())
            }
            TyKind::Array(ty, sz) => {
                let sz_i = self.array_size_value(sz);
                self.encode_array_type(*ty, sz_i.into())
            }
            // In this case, we use what's expected to be the correct variable name for that type parameter.
            TyKind::Param(ParamTy { index, name }) => {
                EncodedType(Expr::PVar(type_param_name(*index, *name)))
            }
            TyKind::Alias(AliasKind::Projection, AliasTy { args, def_id, .. }) => {
                let name = self.tcx().item_name(*def_id);
                let args: Vec<_> = args
                    .iter()
                    .filter_map(|a| self.encode_generic_arg(a))
                    .map(|a| a.0)
                    .collect();
                EncodedType([Expr::from("proj"), name.as_str().into(), args.into()].into())
            }
            _ => fatal!(self, "Cannot encode this type yet: {:#?}", ty.kind()),
        }
    }
}

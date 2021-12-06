use super::place::{GilPlace, GilProj};
use crate::prelude::*;

#[derive(Debug)]
pub enum TypeInStoreEncoding {
    Value,
    List(Vec<TypeInStoreEncoding>),
}

impl<'tcx> TypeInStoreEncoding {
    pub fn uninitialized(&self) -> Literal {
        match self {
            Self::Value => Literal::Undefined,
            Self::List(v) => Literal::LList(v.iter().map(|x| x.uninitialized()).collect()),
        }
    }
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn type_in_store_encoding(&self, ty: Ty<'tcx>) -> TypeInStoreEncoding {
        use TyKind::*;
        match ty.kind() {
            Bool | Char | Int(..) | Uint(..) | Float(..) | Ref(..) | RawPtr(..) => {
                TypeInStoreEncoding::Value
            }
            Tuple(_) => TypeInStoreEncoding::List(
                ty.tuple_fields()
                    .map(|t| self.type_in_store_encoding(t))
                    .collect(),
            ),
            Adt(def, subst) if def.is_struct() => TypeInStoreEncoding::List(
                def.all_fields()
                    .map(|x| self.type_in_store_encoding(self.field_def_type(x, subst)))
                    .collect(),
            ),
            // If an enum is encoded for the store, it means that only a discriminant access will be executed,
            // Therefore, there are no fields.
            Adt(def, _subst) if def.is_enum() => {
                TypeInStoreEncoding::List(vec![TypeInStoreEncoding::Value])
            }
            _ => panic!("Cannot handle type yet: {:#?}", ty),
        }
    }

    /// Returns the expressions that corresponds to reading a value in the store at some place
    pub fn reader_expr_for_place_in_store(&self, place: &GilPlace<'tcx>) -> Expr {
        let init = Expr::PVar(place.base.clone());
        place.proj.iter().fold(init, |curr, next| match next {
            GilProj::Field(u) => Expr::lnth(curr, *u as usize),
            GilProj::Downcast(..) => panic!("READ: Downcast should never be used in the store!"),
        })
    }

    pub fn writer_expr_for_place_in_store(
        &self,
        to_write: Expr,
        place: &GilPlace<'tcx>,
        enc: &TypeInStoreEncoding,
    ) -> Expr {
        fn rec_call(
            base: Expr,
            mut rev_rest: Vec<GilProj>,
            rest_enc: &TypeInStoreEncoding,
            to_write: Expr,
        ) -> Expr {
            if rev_rest.is_empty() {
                return to_write;
            }
            // If the proj is not empty, the encoding has to be a list
            let rest_enc_vec = match rest_enc {
                TypeInStoreEncoding::List(v) => v,
                TypeInStoreEncoding::Value => {
                    panic!("Invalid encoding for given projection:\nENCODING: {:#?}\nPROJ: {:#?}\nBASE: {:#?}", rest_enc, rev_rest, base)
                }
            };
            let curr_proj = rev_rest.pop().unwrap();
            let curr_proj: usize = match curr_proj {
                GilProj::Field(i) => i as usize,
                GilProj::Downcast(..) =>
                // The reason that holds is because you can only put scalars,
                // tuples and structs in memory.
                {
                    panic!("WRITE: Downcast should never happen to values in the store")
                }
            };
            let new_base = Expr::lnth(base.clone(), curr_proj);
            let expr_for_proj = rec_call(
                new_base,
                rev_rest,
                rest_enc_vec.get(curr_proj).unwrap(),
                to_write,
            );
            let mut vec_of_rewrites = Vec::with_capacity(rest_enc_vec.len());
            for i in 0..curr_proj {
                vec_of_rewrites.push(Expr::lnth(base.clone(), i))
            }
            vec_of_rewrites.push(expr_for_proj);
            for i in curr_proj + 1..rest_enc_vec.len() {
                vec_of_rewrites.push(Expr::lnth(base.clone(), i))
            }
            Expr::EList(vec_of_rewrites)
        }
        let base = Expr::PVar(place.base.clone());
        let mut rev_proj = place.proj.clone();
        rev_proj.reverse();
        rec_call(base, rev_proj, enc, to_write)
    }
}

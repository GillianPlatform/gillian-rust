use crate::prelude::*;

pub enum TypeEncoding {
    Nothing,
    Val,
    List(Vec<TypeEncoding>),
}

impl TypeEncoding {
    /// Produces a literal corresponding to the uninitialized value of this type
    pub fn to_uninitialized(&self) -> Literal {
        match self {
            Self::Nothing => Literal::Nono,
            Self::Val => Literal::Undefined,
            Self::List(vec) => {
                let content = vec.iter().map(|y| y.to_uninitialized()).collect();
                Literal::LList(content)
            }
        }
    }
}

impl<'tcx> GilCtxt<'tcx> {
    pub fn encode_type(&self, ty: Ty) -> TypeEncoding {
        use TyKind::*;
        match &ty.kind() {
            Never => TypeEncoding::Nothing,
            Bool | Char | Int(_) | Uint(_) | Float(_) => TypeEncoding::Val,
            Ref(..) => TypeEncoding::Val, // This is probably going to be a pointer
            Tuple(_) => {
                let mut list_vec = vec![];
                for field in ty.tuple_fields() {
                    list_vec.push(self.encode_type(field));
                }
                TypeEncoding::List(list_vec)
            }
            kind => fatal!(self, "Cannot encode type! {:#?}", kind),
        }
    }
}

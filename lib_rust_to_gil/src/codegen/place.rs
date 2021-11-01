use crate::prelude::*;

#[derive(Debug)]
pub enum PlaceEncoding {
    Var(Local), // The encoding is simply the variable
    ListAccess {
        lst: Box<PlaceEncoding>,
        idx: u32,
        size: u32,
    }, // In GIL, this place is going to be an element in a list of known total size
}

impl PlaceEncoding {
    pub fn is_var(&self) -> bool {
        match &self {
            Self::ListAccess { .. } => false,
            Self::Var(_) => true,
        }
    }

    pub fn base(&self) -> Local {
        match self {
            Self::ListAccess { lst: box enc, .. } => enc.base(),
            Self::Var(loc) => *loc,
        }
    }
}

impl<'tcx> GilCtxt<'tcx> {
    /* Returns the variable name. It should also probably return a Vec of commands to get there */
    pub fn encode_place(&self, place: &Place<'tcx>) -> PlaceEncoding {
        let mut encoding = PlaceEncoding::Var(place.local);
        for i in 0..place.projection.len() {
            let parent_ty = self.place_ty_until(place, i);
            match place.projection[i] {
                ProjectionElem::Field(k, _ty) if matches!(parent_ty.kind(), TyKind::Tuple(_)) => {
                    let mut size = 0;
                    parent_ty.tuple_fields().for_each(|_| size += 1);
                    encoding = PlaceEncoding::ListAccess {
                        lst: Box::new(encoding),
                        idx: k.as_u32(),
                        size,
                    };
                }
                ProjectionElem::Index(local) => fatal!(self, "Index with local: {:#?}", local),
                _ => fatal!(
                    self,
                    "So far: {:#?}, but unhandled projection element: {:#?}",
                    encoding,
                    place.projection[i]
                ),
            }
        }
        encoding
    }

    pub fn place_read(&self, enc: &PlaceEncoding) -> Expr {
        match &enc {
            PlaceEncoding::Var(local) => Expr::PVar(self.name_from_local(&local)),
            PlaceEncoding::ListAccess { lst, idx, .. } => Expr::lnth(self.place_read(lst), *idx),
        }
    }

    /// Returns the variable name associated with the place base
    pub fn place_base(&self, enc: &PlaceEncoding) -> String {
        self.name_from_local(&enc.base())
    }

    /// Returns an expression where the place is override by the given expression in the base
    /// For example, if the place is x.0, and x is a tuple of size 3.
    /// `place.expr_override(e)` will return `{{ e, l-nth(x, 1), l-nth(x, 2) }}`
    pub fn place_override(&self, enc: &PlaceEncoding, place_override: Expr) -> Expr {
        match &enc {
            PlaceEncoding::Var(_) => place_override,
            PlaceEncoding::ListAccess { lst, idx, size } => {
                let parent_read = self.place_read(lst);
                let mut vec = Vec::<Expr>::with_capacity(*size as usize);
                for i in 0..*idx {
                    vec.push(Expr::lnth(parent_read.clone(), i));
                }
                vec.push(place_override);
                for i in *idx + 1..*size {
                    vec.push(Expr::lnth(parent_read.clone(), i));
                }
                self.place_override(lst, Expr::EList(vec))
            }
        }
    }

    pub fn push_assignment(&mut self, target: &PlaceEncoding, assigned_expr: Expr) {
        self.push_cmd(Cmd::Assignment {
            variable: self.place_base(target),
            assigned_expr: self.place_override(target, assigned_expr),
        })
    }
}

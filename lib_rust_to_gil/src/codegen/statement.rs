use crate::{codegen::memory::MemoryAction, prelude::*};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let compiled_rvalue = self.push_encode_rvalue(rvalue);
                self.push_place_write(place, compiled_rvalue, self.rvalue_ty(rvalue));
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => match self.push_get_place_access(place) {
                PlaceAccess::InMemory(gp) => {
                    let target = names::unused_var();
                    let (location, projection) = gp.into_loc_proj();
                    let discr = variant_index.as_u32();
                    let action = MemoryAction::StoreDiscriminant {
                        location,
                        projection,
                        discr,
                    };
                    self.push_action(target, action)
                }
                PlaceAccess::InStore(gp) => {
                    let variant_ty = self.place_ty(place);
                    let uninit: Option<Literal> = if let TyKind::Adt(def, subst) = variant_ty.kind()
                    {
                        let v_def = def.variants.get(*variant_index).unwrap();
                        if v_def.fields.is_empty() {
                            None
                        } else {
                            let fields = v_def
                                .fields
                                .iter()
                                .map(|field| {
                                    self.type_in_store_encoding(field.ty(self.ty_ctxt, subst))
                                        .uninitialized()
                                })
                                .collect::<Vec<_>>()
                                .into();
                            Some(fields)
                        }
                    } else {
                        fatal!(
                            self,
                            "Setting discriminant for something that is not a variant {:#?}",
                            variant_ty
                        );
                    };
                    let new_value: Expr = match uninit {
                        Some(uninit) => {
                            vec![Expr::int(variant_index.as_u32() as i64), uninit.into()].into()
                        }
                        None => vec![Expr::int(variant_index.as_u32() as i64)].into(),
                    };
                    // Some of the following is copy-pasted from place::push_place_write
                    // it could probably be factored out
                    let enc = self.type_in_store_encoding(self.place_ty(&place.local.into()));
                    let write_expr = self.writer_expr_for_place_in_store(new_value, &gp, &enc);
                    let assign = Cmd::Assignment {
                        variable: gp.base,
                        assigned_expr: write_expr,
                    };
                    self.push_cmd(assign);
                }
            },
            _ => fatal!(self, "Statement not handled yet: {:#?}", stmt),
        }
    }
}

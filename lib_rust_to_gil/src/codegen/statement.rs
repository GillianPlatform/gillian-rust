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
            } => {
                let gp = self.push_get_gil_place(place);

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
            StatementKind::FakeRead(..)
            | StatementKind::Nop
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::AscribeUserType(..) => {}

            _ => fatal!(self, "Statement not handled yet: {:#?}", stmt),
        }
    }
}

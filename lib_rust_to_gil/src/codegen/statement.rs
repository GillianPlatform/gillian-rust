use rustc_middle::ty::Region;

use crate::prelude::*;

use super::typ_encoding::region_name;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn create_region(&mut self, region: Region<'tcx>) {
        if region.is_var() && self.activated_borrows.insert(region.as_var()) {
            self.push_create_lifetime(region_name(region).unwrap())
        }
    }

    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let compiled_rvalue = self.push_encode_rvalue(rvalue);

                if let Some(r) = region(place.ty(&self.mir().local_decls, self.tcx()).ty) {
                    self.create_region(r)
                }

                self.push_place_write(*place, compiled_rvalue, self.rvalue_ty(rvalue));
            }
            StatementKind::Deinit(box place) => self.push_deinit_place(*place),
            StatementKind::SetDiscriminant { .. } => {
                let cmd = Cmd::Fail {
                    name: "SET_DISCR".to_owned(),
                    parameters: vec!["This statement only exists so we can compile constructors because they exist in MIR, but shouldn't be used".into()],
                };
                self.push_cmd(cmd);
            }
            StatementKind::PlaceMention(..)
            | StatementKind::FakeRead(..)
            | StatementKind::Nop
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::AscribeUserType(..) => {}

            _ => fatal!(self, "Statement not handled yet: {:#?}", stmt),
        }
    }
}

fn region(ty: Ty<'_>) -> Option<Region<'_>> {
    match ty.kind() {
        TyKind::Ref(r, _, _) => Some(*r),
        _ => None,
    }
}

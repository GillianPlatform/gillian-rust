use crate::prelude::*;

const ALLOC_ACTION_NAME: &str = "mem_alloc";
const LOAD_ACTION_NAME: &str = "mem_load";
const STORE_ACTION_NAME: &str = "mem_store";
const LOAD_DISCR_ACTION_NAME: &str = "mem_load_discr";
const STORE_DISCR_ACTION_NAME: &str = "mem_store_discr";

pub enum MemoryAction<'tcx> {
    Alloc(Ty<'tcx>),
    Load {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
        copy: bool,
    },
    Store {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
        value: Expr,
    },
    LoadDiscriminant {
        location: Expr,
        projection: Expr,
    },
    StoreDiscriminant {
        location: Expr,
        projection: Expr,
        discr: u32,
    },
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_alloc_into_local(&mut self, local: Local, typ: Ty<'tcx>) {
        let action = MemoryAction::Alloc(typ);
        let target = self.name_from_local(&local);
        self.push_action(target, action);
    }

    pub fn push_action(&mut self, target: String, action: MemoryAction<'tcx>) {
        match action {
            MemoryAction::Alloc(ty) => {
                let ty = Expr::Lit(self.encode_type(ty));
                log::debug!("Allocating: {}", &ty);
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: ALLOC_ACTION_NAME.to_string(),
                    parameters: vec![ty],
                })
            }
            MemoryAction::Load {
                location,
                projection,
                typ,
                copy,
            } => {
                let temp = self.temp_var();
                let encoded_typ = self.encode_type(typ);
                self.push_cmd(Cmd::Action {
                    variable: temp.clone(),
                    action_name: LOAD_ACTION_NAME.to_string(),
                    parameters: vec![
                        location,
                        projection,
                        Expr::Lit(encoded_typ),
                        Expr::bool(copy),
                    ],
                });
                self.push_cmd(Cmd::Assignment {
                    variable: target,
                    assigned_expr: Expr::lnth(Expr::PVar(temp), 0),
                })
            }
            MemoryAction::Store {
                location,
                projection,
                typ,
                value,
            } => {
                let encoded_typ = self.encode_type(typ);
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: STORE_ACTION_NAME.to_string(),
                    parameters: vec![location, projection, Expr::Lit(encoded_typ), value],
                })
            }
            MemoryAction::LoadDiscriminant {
                location,
                projection,
            } => self.push_cmd(Cmd::Action {
                variable: target,
                action_name: LOAD_DISCR_ACTION_NAME.to_string(),
                parameters: vec![location, projection],
            }),
            MemoryAction::StoreDiscriminant {
                location,
                projection,
                discr,
            } => self.push_cmd(Cmd::Action {
                variable: target,
                action_name: STORE_DISCR_ACTION_NAME.to_string(),
                parameters: vec![location, projection, Expr::int(discr as i64).into()],
            }),
        };
    }
}

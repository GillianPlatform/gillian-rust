use crate::prelude::*;

const ALLOC_ACTION_NAME: &str = "mem_alloc";
const LOAD_ACTION_NAME: &str = "mem_load";
const STORE_ACTION_NAME: &str = "mem_store";

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
}

impl<'tcx> GilCtxt<'tcx> {
    pub fn push_alloc_into_local(&mut self, local: Local, typ: Ty<'tcx>) {
        let action = MemoryAction::Alloc(typ);
        let target = self.name_from_local(&local);
        self.push_action(target, action);
    }

    pub fn push_action(&mut self, target: String, action: MemoryAction<'tcx>) {
        let cmd = match action {
            MemoryAction::Alloc(ty) => Cmd::Action {
                variable: target,
                action_name: ALLOC_ACTION_NAME.to_string(),
                parameters: vec![Expr::Lit(self.encode_type(ty))],
            },
            MemoryAction::Load {
                location,
                projection,
                typ,
                copy,
            } => Cmd::Action {
                variable: target,
                action_name: LOAD_ACTION_NAME.to_string(),
                parameters: vec![
                    location,
                    projection,
                    Expr::Lit(self.encode_type(typ)),
                    Expr::bool(copy),
                ],
            },
            MemoryAction::Store {
                location,
                projection,
                typ,
                value,
            } => Cmd::Action {
                variable: target,
                action_name: STORE_ACTION_NAME.to_string(),
                parameters: vec![
                    location,
                    projection,
                    Expr::Lit(self.encode_type(typ)),
                    value,
                ],
            },
        };
        self.push_cmd(cmd);
    }
}

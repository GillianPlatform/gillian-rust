use crate::prelude::*;

pub(crate) mod action_names {
    pub(crate) const ALLOC: &str = "alloc";
    pub(crate) const LOAD_VALUE: &str = "load_value";
    pub(crate) const STORE_VALUE: &str = "store_value";
    pub(crate) const DEINIT: &str = "deinit";
    pub(crate) const FREE: &str = "free";
    pub(crate) const LOAD_DISCR: &str = "load_discr";
}

pub enum MemoryAction<'tcx> {
    Alloc(Ty<'tcx>),
    LoadValue {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
        copy: bool,
    },
    StoreValue {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
        value: Expr,
    },
    Deinit {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
    },
    Free {
        location: Expr,
        projection: Expr,
        typ: Ty<'tcx>,
    },
    LoadDiscriminant {
        location: Expr,
        projection: Expr,
        enum_typ: Ty<'tcx>,
    },
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_alloc_into_local(&mut self, local: Local, typ: Ty<'tcx>) {
        let action = MemoryAction::Alloc(typ);
        let target = self.name_from_local(local);
        self.push_action(target, action);
    }

    pub fn push_free_local(&mut self, local: Local, typ: Ty<'tcx>) {
        let target = names::unused_var();
        let local = self.name_from_local(local);
        let location = Expr::lnth(Expr::PVar(local.clone()), 0);
        let projection = Expr::lnth(Expr::PVar(local), 1);

        let action = MemoryAction::Free {
            location,
            projection,
            typ,
        };
        self.push_action(target, action);
    }

    pub fn push_action(&mut self, target: String, action: MemoryAction<'tcx>) {
        match action {
            MemoryAction::Alloc(ty) => {
                let ty = self.encode_type(ty).into();
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: action_names::ALLOC.to_string(),
                    parameters: vec![ty],
                });
            }
            MemoryAction::LoadValue {
                location,
                projection,
                typ,
                copy,
            } => {
                let temp = self.temp_var();
                let encoded_typ = self.encode_type(typ).into();
                self.push_cmd(Cmd::Action {
                    variable: temp.clone(),
                    action_name: action_names::LOAD_VALUE.to_string(),
                    parameters: vec![location, projection, encoded_typ, Expr::bool(copy)],
                });
                self.push_cmd(Cmd::Assignment {
                    variable: target,
                    assigned_expr: Expr::lnth(Expr::PVar(temp), 0),
                })
            }
            MemoryAction::StoreValue {
                location,
                projection,
                typ,
                value,
            } => {
                let encoded_typ = self.encode_type(typ).into();
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: action_names::STORE_VALUE.to_string(),
                    parameters: vec![location, projection, encoded_typ, value],
                })
            }
            MemoryAction::Deinit {
                location,
                projection,
                typ,
            } => {
                let encoded_typ = self.encode_type(typ).into();
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: action_names::DEINIT.to_string(),
                    parameters: vec![location, projection, encoded_typ],
                })
            }
            MemoryAction::Free {
                location,
                projection,
                typ,
            } => {
                let encoded_typ = self.encode_type(typ).into();
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: action_names::FREE.to_string(),
                    parameters: vec![location, projection, encoded_typ],
                })
            }
            MemoryAction::LoadDiscriminant {
                location,
                projection,
                enum_typ,
            } => {
                let temp = self.temp_var();
                let encoded_typ = self.encode_type(enum_typ).into();
                self.push_cmd(Cmd::Action {
                    variable: temp.clone(),
                    action_name: action_names::LOAD_DISCR.to_string(),
                    parameters: vec![location, projection, encoded_typ],
                });
                self.push_cmd(Cmd::Assignment {
                    variable: target,
                    assigned_expr: Expr::PVar(temp).lnth(0),
                })
            }
        };
    }
}

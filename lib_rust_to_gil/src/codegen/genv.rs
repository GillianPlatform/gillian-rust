use crate::prelude::*;
use rustc_middle::ty::AdtDef;
use std::collections::{HashSet, VecDeque};

static DECLARE_TYPE_ACTION: &str = "genv_decl_type";

pub struct GlobalEnv<'tcx> {
    /// The types that should be encoded for the GIL global env
    tcx: TyCtxt<'tcx>,
    types_in_queue: VecDeque<Ty<'tcx>>,
    encoded_types: HashSet<Ty<'tcx>>,
}

impl<'tcx> TypeEncoderable<'tcx> for GlobalEnv<'tcx> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>) {
        self.add_type(ty);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did).to_string()
    }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            types_in_queue: Default::default(),
            encoded_types: Default::default(),
        }
    }

    // Panics if not called with an ADT
    fn type_decl_action(&mut self, ty: Ty<'tcx>) -> ProcBodyItem {
        let (name, kind, decl) = match ty.kind() {
            TyKind::Adt(def, subst) if def.is_struct() => {
                let name = self.tcx.item_name(def.did).to_string();
                let fields: Vec<Literal> = def
                    .all_fields()
                    .map(|field| {
                        let name = Literal::from(self.tcx.item_name(field.did).to_string());
                        let typ = self.encode_type(field.ty(self.tcx, subst));
                        vec![name, typ].into()
                    })
                    .collect();
                (name, "struct", fields.into())
            }
            _ => panic!(
                "This function should never be called with this type {:#?}",
                ty
            ),
        };
        Cmd::Action {
            variable: names::unused_var(),
            action_name: DECLARE_TYPE_ACTION.into(),
            parameters: vec![name.into(), kind.into(), Expr::Lit(decl)],
        }
        .into()
    }

    pub fn add_type(&mut self, ty: Ty<'tcx>) {
        if !(self.encoded_types.contains(ty) || self.types_in_queue.contains(&ty)) {
            self.types_in_queue.push_back(ty);
        }
    }

    pub fn declaring_proc(mut self) -> Proc {
        let mut body: Vec<ProcBodyItem> = vec![];
        while !self.types_in_queue.is_empty() {
            let ty = self.types_in_queue.pop_front().unwrap();
            body.push(self.type_decl_action(ty));
        }
        body.push(
            Cmd::Assignment {
                variable: names::ret_var(),
                assigned_expr: Expr::undefined(),
            }
            .into(),
        );
        body.push(Cmd::ReturnNormal.into());
        Proc::new(names::global_env_proc(), vec![], body)
    }
}

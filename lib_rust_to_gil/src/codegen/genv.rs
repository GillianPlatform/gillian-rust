use crate::prelude::*;
use std::collections::HashSet;

static DECLARE_TYPE_ACTION: &str = "genv_decl_type";

#[derive(Default)]
pub struct GlobalEnv<'tcx> {
    /// The types that should be encoded for the GIL global env
    types: HashSet<Ty<'tcx>>,
}

// Panics if not called with an ADT
fn type_decl_action(ty: Ty, tcx: &TyCtxt) -> ProcBodyItem {
    let (name, kind, decl) = match ty.kind() {
        TyKind::Adt(def, _subst) if def.is_struct() => {
            let name = tcx.item_name(def.did).to_string();
            let fields: Vec<Literal> = def
                .all_fields()
                .map(|field| {
                    let name = Literal::from(tcx.item_name(field.did).to_string());
                    let typ = Literal::Undefined;
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

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_type(&mut self, ty: Ty<'tcx>) {
        self.types.insert(ty);
    }

    pub fn declaring_proc(self, tcx: &TyCtxt) -> Proc {
        let body: Vec<ProcBodyItem> = self
            .types
            .into_iter()
            .map(|ty| type_decl_action(ty, tcx))
            .collect();
        Proc::new(names::global_env_proc(), vec![], body)
    }
}

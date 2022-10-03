use crate::prelude::*;
use rustc_middle::ty::{AdtDef, ReprOptions};
use std::collections::{HashSet, VecDeque};

const DECLARE_TYPE_ACTION: &str = "genv_decl_type";

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum CustomRuntime<'tcx> {
    PtrPlus(Ty<'tcx>, String),
}

pub struct GlobalEnv<'tcx> {
    /// The types that should be encoded for the GIL global env
    tcx: TyCtxt<'tcx>,
    types_in_queue: VecDeque<Ty<'tcx>>,
    encoded_types: HashSet<Ty<'tcx>>,
    runtime_to_encode: HashSet<CustomRuntime<'tcx>>,
}

impl<'tcx> CanFatal for GlobalEnv<'tcx> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

impl<'tcx> TypeEncoder<'tcx> for GlobalEnv<'tcx> {
    fn add_type_to_genv(&mut self, ty: Ty<'tcx>) {
        self.add_type(ty);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            types_in_queue: Default::default(),
            encoded_types: Default::default(),
            runtime_to_encode: Default::default(),
        }
    }

    fn encode_repr(&self, repr: &ReprOptions) -> Literal {
        if repr.int.is_some() || repr.align.is_some() || repr.pack.is_some() {
            fatal!(
                self,
                "Cant handle this specific representations at the moment, only C"
            )
        };
        if repr.c() {
            "c".into()
        } else {
            "rust".into()
        }
    }

    // Panics if not called with an ADT
    fn type_decl_action(&mut self, ty: Ty<'tcx>) -> ProcBodyItem {
        let (name, decl) = match ty.kind() {
            TyKind::Adt(def, subst) if def.is_struct() => {
                if def.has_ctor() {
                    fatal!(self, "Can't handle struct with constructors yet");
                }
                if def.is_variant_list_non_exhaustive() {
                    fatal!(self, "Can't handle #[non_exhaustive] yet");
                }
                let name = self.tcx.item_name(def.did()).to_string();
                let fields: Vec<Literal> = def
                    .all_fields()
                    .map(|field| {
                        let name = Literal::from(self.tcx.item_name(field.did).to_string());
                        let typ = self.encode_type(field.ty(self.tcx, subst));
                        vec![name, typ.into()].into()
                    })
                    .collect();
                let decl: Literal = vec![
                    "struct".into(),
                    fields.into(),
                    self.encode_repr(&def.repr()),
                ]
                .into();
                (name, decl.into())
            }
            TyKind::Adt(def, subst) if def.is_enum() => {
                if def.is_variant_list_non_exhaustive() {
                    fatal!(self, "Can't handle #[non_exhaustive] yet");
                }
                let name = self.tcx.item_name(def.did()).to_string();
                let variants: Vec<Literal> = def
                    .variants()
                    .iter()
                    .map(|variant| {
                        let fields: Literal = variant
                            .fields
                            .iter()
                            .map(|field| self.encode_type(field.ty(self.tcx, subst)).into())
                            .collect::<Vec<_>>()
                            .into();
                        let name = self.tcx.item_name(variant.def_id).to_string();
                        vec![name.into(), fields].into()
                    })
                    .collect();
                let decl: Literal = vec!["variant".into(), variants.into()].into();
                (name, decl.into())
            }
            _ => panic!(
                "This function should never be called with this type {:#?}",
                ty
            ),
        };
        Cmd::Action {
            variable: names::unused_var(),
            action_name: DECLARE_TYPE_ACTION.into(),
            parameters: vec![name.into(), decl],
        }
        .into()
    }

    pub fn add_type(&mut self, ty: Ty<'tcx>) {
        if !(self.encoded_types.contains(&ty) || self.types_in_queue.contains(&ty)) {
            self.types_in_queue.push_back(ty);
        }
    }

    pub fn add_runtime(&mut self, r: CustomRuntime<'tcx>) {
        self.runtime_to_encode.insert(r);
    }

    fn declaring_proc(&mut self) -> Proc {
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

    fn proc_of_custom_runtime(&mut self, r: CustomRuntime<'tcx>) -> Proc {
        match r {
            CustomRuntime::PtrPlus(ty, fname) => self.ptr_plus_impl(ty, fname),
        }
    }

    pub fn add_all_procs(mut self, prog: &mut Prog) {
        let runtime = self.runtime_to_encode.clone();
        for r in runtime {
            prog.add_proc(self.proc_of_custom_runtime(r))
        }
        // Importantly, this has to be done after pushing the custom runtime!
        prog.add_proc(self.declaring_proc());
    }
}

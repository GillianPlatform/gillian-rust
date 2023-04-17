use super::utils::get_thir;
use gillian::gil::Lemma;
use rustc_hir::def_id::DefId;
use rustc_middle::thir::{Param, Pat, PatKind};
use rustc_middle::ty::{AdtDef, TyCtxt, WithOptConstParam};

use gillian::gil::Assertion;

use crate::codegen::typ_encoding::lifetime_param_name;
use crate::utils::polymorphism::HasGenericLifetimes;
use crate::{
    codegen::typ_encoding::type_param_name,
    codegen::{genv::GlobalEnv, typ_encoding::TypeEncoder},
    prelude::{fatal, HasDefId, HasTyCtxt},
    utils::polymorphism::HasGenericArguments,
};

struct LemmaSig {
    name: String,
    params: Vec<String>,
}

pub(crate) struct LemmaCtx<'tcx, 'genv> {
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    did: DefId,
    trusted: bool,
}

impl<'tcx, 'genv> HasTyCtxt<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl HasDefId for LemmaCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

impl<'tcx> HasGenericArguments<'tcx> for LemmaCtx<'tcx, '_> {}
impl<'tcx> HasGenericLifetimes<'tcx> for LemmaCtx<'tcx, '_> {}

impl<'tcx, 'genv> TypeEncoder<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.global_env.add_adt(def);
    }

    fn adt_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}

impl<'tcx, 'genv> LemmaCtx<'tcx, 'genv> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        global_env: &'genv mut GlobalEnv<'tcx>,
        did: DefId,
        trusted: bool,
    ) -> Self {
        Self {
            tcx,
            global_env,
            did,
            trusted,
        }
    }

    fn extract_param(&self, param: &Param<'tcx>) -> String {
        match &param.pat {
            Some(box Pat {
                kind:
                    PatKind::Binding {
                        mutability: _,
                        name,
                        var: _,
                        subpattern,
                        is_primary,
                        mode: _,
                        ty: _,
                    },
                ..
            }) => {
                if !is_primary {
                    fatal!(self, "Predicate parameters must be primary");
                }
                if subpattern.is_some() {
                    fatal!(self, "Predicate parameters cannot have subpatterns");
                }
                name.to_string()
            }
            _ => fatal!(self, "Predicate parameters must be variables"),
        }
    }

    fn lemma_name(&self) -> String {
        self.tcx.def_path_str(self.did)
    }

    fn sig(&self) -> LemmaSig {
        get_thir!(thir, _expr, self);
        let lft_params = self
            .generic_lifetimes()
            .into_iter()
            .map(|x| lifetime_param_name(&x));
        let type_params = self
            .generic_types()
            .into_iter()
            .map(|x| type_param_name(x.0, x.1));
        let args = thir.params.iter().map(|p| self.extract_param(p));
        let params = lft_params.chain(type_params).chain(args).collect();
        LemmaSig {
            name: self.lemma_name(),
            params,
        }
    }

    pub(crate) fn compile(self) -> Lemma {
        let sig = self.sig();
        if self.trusted {
            // We set temporary hyp and conclusion, which we be replaced later by the specs
            Lemma {
                name: sig.name,
                params: sig.params,
                hyp: Assertion::Emp,
                concs: Vec::new(),
                variant: None,
                existentials: Vec::new(),
            }
        } else {
            fatal!(self, "Can't compile untrusted lemmas yet")
        }
    }
}

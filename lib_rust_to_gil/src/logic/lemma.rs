use super::LogicItem;
use crate::signature::{build_signature, ParamKind};
use crate::{prelude::*, signature};
use gillian::gil::{Assertion, Expr, LCmd, Lemma, SLCmd};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgs;

use crate::temp_gen::TempGenerator;
use crate::{
    codegen::typ_encoding::TypeEncoder,
    prelude::{fatal, HasDefId, HasTyCtxt},
};

struct LemmaSig {
    name: String,
    params: Vec<String>,
}

pub(crate) struct LemmaCtx<'tcx, 'genv> {
    global_env: &'genv mut GlobalEnv<'tcx>,
    did: DefId,
    temp_gen: &'genv mut TempGenerator,
    trusted: bool,
}

impl<'tcx, 'genv> HasTyCtxt<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.global_env.tcx()
    }
}

impl HasDefId for LemmaCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

impl<'tcx> HasGlobalEnv<'tcx> for LemmaCtx<'tcx, '_> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx> {
        self.global_env
    }

    fn global_env(&self) -> &GlobalEnv<'tcx> {
        self.global_env
    }
}

impl<'tcx> TypeEncoder<'tcx> for LemmaCtx<'tcx, '_> {}

impl<'tcx, 'genv> LemmaCtx<'tcx, 'genv> {
    pub fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        did: DefId,
        temp_gen: &'genv mut TempGenerator,
        trusted: bool,
    ) -> Self {
        Self {
            global_env,
            did,
            trusted,
            temp_gen,
        }
    }

    fn lemma_name(&self) -> String {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        self.global_env.just_pred_name_with_args(self.did, args)
    }

    fn sig(&mut self) -> LemmaSig {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        let sig = build_signature(self.global_env, self.did(), args, &mut self.temp_gen);
        let params = sig.physical_args().map(|a| a.name().to_string()).collect();
        LemmaSig {
            name: self.lemma_name(),
            params,
        }
    }

    pub(crate) fn compile(mut self) -> Lemma {
        let sig = self.sig();

        if !self.trusted {
            fatal!(self, "Can't compile untrusted lemmas yet")
        }

        let name = sig.name.clone();

        // We set temporary hyp and conclusion, which we be replaced later by the specs
        let mut lemma = Lemma {
            name: name.clone(),
            params: sig.params,
            hyp: Assertion::Emp,
            concs: Vec::new(),
            proof: None,
            variant: None,
            existentials: Vec::new(),
        };
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        let sig = build_signature(self.global_env, self.did, args, self.temp_gen);

        let ss = sig
            .to_gil_spec(self.global_env, name)
            .expect("Expected lemma to have contract")
            .sspecs
            .remove(0);

        lemma.hyp = ss.pre;
        lemma.concs = ss.posts;

        lemma
    }
}

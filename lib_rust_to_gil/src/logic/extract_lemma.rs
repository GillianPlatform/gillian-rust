use super::gilsonite::GilsoniteBuilder;
use super::{utils::get_thir, LogicItem};
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

impl<'tcx> HasTyCtxt<'tcx> for ExtractLemmaCtx<'tcx, '_> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.global_env.tcx()
    }
}

impl HasDefId for ExtractLemmaCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

pub(crate) struct ExtractLemmaCtx<'tcx, 'genv> {
    global_env: &'genv mut GlobalEnv<'tcx>,
    did: DefId,
    temp_gen: &'genv mut TempGenerator,
    trusted: bool,
    name: String,
}

impl<'tcx, 'genv> ExtractLemmaCtx<'tcx, 'genv> {
    pub fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        did: DefId,
        temp_gen: &'genv mut TempGenerator,
        trusted: bool,
    ) -> Self {
        let name = global_env.extract_lemma_name(did);
        Self {
            global_env,
            did,
            trusted,
            temp_gen,
            name,
        }
    }

    fn proof_name(&self) -> String {
        self.name.clone() + "$$extract_proof"
    }

    fn pre_name(&self) -> String {
        self.name.clone() + "$$pre"
    }

    fn post_name(&self) -> String {
        self.name.clone() + "$$post"
    }

    pub fn compile(&mut self) -> Vec<LogicItem> {
        let term = {
            let (thir, e) = get_thir!(self.global_env, self.did);
            let g = GilsoniteBuilder::new(thir.clone(), self.tcx());
            if self.global_env.config.prophecies {
                g.build_extract_lemma_proph(e)
            } else {
                g.build_extract_lemma_no_proph(e)
            }
        };

        let args = GenericArgs::identity_for_item(self.tcx(), self.did());

        // let mut sig = signature::build_signature(self.global_env, self.did, args, self.temp_gen);

        // We are going to create three items:
        // - The wand's precondition
        // - The wand's postcondition
        // - The lemma itself, together with its proof
        let mut res: Vec<LogicItem> = Vec::with_capacity(3);

        // First we construct the wand's precondition.
        // It is just the "extract" call with the proper arguments,
        // i.e. passed arguments except lifetime variable
        let extract_call = term.extract;

        let inner_pre = self
            .global_env
            .resolve_inner_pred(extract_call.def_id, extract_call.substs);

        fatal!(self.global_env, "Inner predicate: {inner_pre}");

        // let (inner_predicate_name, pre_inner_args, guard) = {
        //     let mut splat = sig
        //         .user_pre()
        //         .expect("extract lemma needs precondition")
        //         .clone()
        //         .unstar();

        //     let Assertion::Pred { name, params } = splat.remove(0) else {
        //         fatal!(self, "malformed precondition for extract lemma")
        //     };
        //     // TODO assert first argument is a lifetime
        //     let mut params = params.clone();
        //     params.remove(0);
        //     (name.clone() + "$$inner", params, splat)
        // };

        // let inner_call = Assertion::Pred {
        //     name: inner_predicate_name,
        //     params: pre_inner_args.clone(),
        // };

        // let non_lvars = sig
        //     .args
        //     .iter()
        //     .skip(1)
        //     .filter(|p| !matches!(p, ParamKind::Logic(_, _)))
        //     .count();
        // let ins = (0..non_lvars).collect();
        // let pre_params = sig
        //     .args
        //     .iter()
        //     .skip(1)
        //     .map(|p| (p.name().to_string(), None))
        //     .collect();

        // let def = sig
        //     .store_eq_var()
        //     .into_iter()
        //     .chain(sig.type_wf_pres(self.global_env))
        //     .chain(guard)
        //     .fold(inner_call, Assertion::star);

        // // let def = spec.pre; // There is a unique assertion in the definitions
        // let proof_pre = Pred {
        //     name: pre_name.clone(),
        //     num_params: 0,
        //     params: pre_params,
        //     ins,
        //     definitions: vec![def],
        //     pure: false,
        //     abstract_: false,
        //     facts: vec![],
        //     guard: None,
        // };

        // res.push(LogicItem::Pred(proof_pre));

        // let (inner_predicate_name, inner_args, remainder) = {
        //     let post = sig.user_post().expect("extract lemma needs precondition");
        //     let mut splat = post.unstar();

        //     let Assertion::Pred { name, params } = splat.remove(0) else {
        //         fatal!(self, "malformed precondition for extract lemma")
        //     };
        //     // TODO assert first argument is a lifetime
        //     let mut params = params.clone();
        //     params.remove(0);

        //     (name.clone() + "$$inner", params, splat)
        // };

        // let inner_call = Assertion::Pred {
        //     name: inner_predicate_name,
        //     params: inner_args,
        // };

        // let post_params: Vec<_> = sig
        //     .args
        //     .iter()
        //     .skip(1)
        //     .map(|p| (p.name().to_string(), None))
        //     .collect();

        // let ins = (0..post_params.len()).collect();

        // // TODO(xavier): Remove and replace with `vars_wf`.
        // let store_eqs = post_params.iter().cloned().map(|(nm, _)| {
        //     Expr::PVar(nm.clone())
        //         .eq_f(Expr::LVar(format!("#{}", nm)))
        //         .into_asrt()
        // });

        // let def = store_eqs
        //     .into_iter()
        //     .chain(sig.type_wf_pres(self.global_env))
        //     .chain(remainder)
        //     .rfold(inner_call, |acc, a| Assertion::star(a, acc));

        // let proof_post = Pred {
        //     name: post_name.clone(),
        //     num_params: 0,
        //     params: post_params.clone(),
        //     ins,
        //     definitions: vec![def],
        //     pure: false,
        //     abstract_: false,
        //     facts: vec![],
        //     guard: None,
        // };
        // res.push(LogicItem::Pred(proof_post));

        // // REALLY HACKY.
        // // TODO(xavier): Clean this up by building the arguments properly from the lemma
        // // signature.
        // let params: Vec<_> = post_params
        //     .iter()
        //     .map(|(e, _)| Expr::LVar(format!("#{e}")))
        //     .collect();

        // let pre_call_tup = (pre_name.clone(), params.clone());
        // let post_call_tup = (post_name.clone(), params.clone());

        // let proof = {
        //     vec![LCmd::SL(SLCmd::Package {
        //         lhs: post_call_tup.clone(),
        //         rhs: pre_call_tup.clone(),
        //     })]
        // };

        // let conc = Assertion::pred_call_of_tuple(post_call_tup.clone())
        //     .clone()
        //     .star(Assertion::wand(post_call_tup, pre_call_tup.clone()));

        // // Something weird about the lifetimes here
        // let params = sig.args.iter().filter_map(|p| match p {
        //     ParamKind::Generic(t) => Some(t.to_string()),
        //     ParamKind::Program(t, _) => Some(t.to_string()),
        //     _ => None,
        // });
        // let proof_lemma = Lemma {
        //     name,
        //     params: params.collect(),
        //     hyp: Assertion::pred_call_of_tuple(pre_call_tup),
        //     concs: vec![conc],
        //     proof: Some(proof),
        //     variant: None,
        //     existentials: vec![],
        // };

        // res.push(LogicItem::Lemma(proof_lemma));
        // res
    }
}

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
    is_extract_lemma: bool,
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
        is_extract_lemma: bool,
    ) -> Self {
        Self {
            global_env,
            did,
            trusted,
            is_extract_lemma,
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

    pub(crate) fn compile(mut self) -> Vec<LogicItem> {
        let mut res = Vec::with_capacity(1 + 3 * (self.is_extract_lemma as usize));

        let sig = self.sig();

        if self.is_extract_lemma {
            let defs = self.compile_extract_lemma(sig.name.clone(), self.did);
            res.extend(defs);
        }
        if self.trusted {
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

            res.push(LogicItem::Lemma(lemma));
        } else {
            fatal!(self, "Can't compile untrusted lemmas yet")
        }
        res
    }

    fn compile_extract_lemma(&mut self, name: String, id: DefId) -> Vec<LogicItem> {
        let name = name.clone() + "$$extract_proof";
        let post_name = name.clone() + "$$post";
        let pre_name = name.clone() + "$$pre";
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());

        let mut sig = signature::build_signature(self.global_env, id, args, &mut self.temp_gen);

        let mut res = Vec::new();

        let (inner_predicate_name, pre_inner_args, guard) = {
            let mut splat = sig
                .user_pre()
                .expect("extract lemma needs precondition")
                .clone()
                .unstar();

            let Assertion::Pred { name, params } = splat.remove(0) else {
                fatal!(self, "malformed precondition for extract lemma")
            };
            // TODO assert first argument is a lifetime
            let mut params = params.clone();
            params.remove(0);
            (name.clone() + "$$inner", params, splat)
        };

        let inner_call = Assertion::Pred {
            name: inner_predicate_name,
            params: pre_inner_args.clone(),
        };

        let non_lvars = sig
            .args
            .iter()
            .skip(1)
            .filter(|p| !matches!(p, ParamKind::Logic(_, _)))
            .count();
        let ins = (0..non_lvars).collect();
        let pre_params = sig
            .args
            .iter()
            .skip(1)
            .map(|p| (p.name().to_string(), None))
            .collect();

        let def = sig
            .store_eq_var()
            .into_iter()
            .chain(sig.type_wf_pres(self.global_env))
            .chain(guard)
            .fold(inner_call, Assertion::star);

        // let def = spec.pre; // There is a unique assertion in the definitions
        let proof_pre = Pred {
            name: pre_name.clone(),
            num_params: 0,
            params: pre_params,
            ins,
            definitions: vec![def],
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: None,
        };

        res.push(LogicItem::Pred(proof_pre));

        let (inner_predicate_name, inner_args, remainder) = {
            let post = sig.user_post().expect("extract lemma needs precondition");
            let mut splat = post.unstar();

            let Assertion::Pred { name, params } = splat.remove(0) else {
                fatal!(self, "malformed precondition for extract lemma")
            };
            // TODO assert first argument is a lifetime
            let mut params = params.clone();
            params.remove(0);

            (name.clone() + "$$inner", params, splat)
        };

        let inner_call = Assertion::Pred {
            name: inner_predicate_name,
            params: inner_args,
        };

        let post_params: Vec<_> = sig
            .args
            .iter()
            .skip(1)
            .map(|p| (p.name().to_string(), None))
            .collect();

        let ins = (0..post_params.len()).collect();

        // TODO(xavier): Remove and replace with `vars_wf`.
        let store_eqs = post_params.iter().cloned().map(|(nm, _)| {
            Expr::PVar(nm.clone())
                .eq_f(Expr::LVar(format!("#{}", nm)))
                .into_asrt()
        });

        let def = store_eqs
            .into_iter()
            .chain(sig.type_wf_pres(self.global_env))
            .chain(remainder)
            .rfold(inner_call, |acc, a| Assertion::star(a, acc));

        let proof_post = Pred {
            name: post_name.clone(),
            num_params: 0,
            params: post_params.clone(),
            ins,
            definitions: vec![def],
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: None,
        };
        res.push(LogicItem::Pred(proof_post));

        // REALLY HACKY.
        // TODO(xavier): Clean this up by building the arguments properly from the lemma
        // signature.
        let params: Vec<_> = post_params
            .iter()
            .map(|(e, _)| Expr::LVar(format!("#{e}")))
            .collect();

        let pre_call_tup = (pre_name.clone(), params.clone());
        let post_call_tup = (post_name.clone(), params.clone());

        let proof = {
            vec![LCmd::SL(SLCmd::Package {
                lhs: post_call_tup.clone(),
                rhs: pre_call_tup.clone(),
            })]
        };

        let conc = Assertion::pred_call_of_tuple(post_call_tup.clone())
            .clone()
            .star(Assertion::wand(post_call_tup, pre_call_tup.clone()));

        // Something weird about the lifetimes here
        let params = sig.args.iter().filter_map(|p| match p {
            ParamKind::Generic(t) => Some(t.to_string()),
            ParamKind::Program(t, _) => Some(t.to_string()),
            _ => None,
        });
        let proof_lemma = Lemma {
            name,
            params: params.collect(),
            hyp: Assertion::pred_call_of_tuple(pre_call_tup),
            concs: vec![conc],
            proof: Some(proof),
            variant: None,
            existentials: vec![],
        };

        res.push(LogicItem::Lemma(proof_lemma));
        res
    }
}

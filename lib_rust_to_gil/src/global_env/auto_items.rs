use rustc_middle::ty::{EarlyBinder, ParamEnv};

use crate::logic::gilsonite::Assert;
use crate::logic::{gilsonite, PredCtx};
use crate::signature::build_signature;
use crate::temp_gen::TempGenerator;
use crate::{prelude::*, temp_gen};

pub(super) struct MonoSpec<'tcx> {
    name: String,
    did: DefId,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> From<MonoSpec<'tcx>> for AutoItem<'tcx> {
    fn from(value: MonoSpec<'tcx>) -> Self {
        Self::MonoSpec(value)
    }
}

impl<'tcx> MonoSpec<'tcx> {
    pub fn new(name: String, did: DefId, args: GenericArgsRef<'tcx>) -> Self {
        Self { name, did, args }
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let mut temp_gen = TempGenerator::new();
        let sig = build_signature(global_env, self.did, self.args, &mut temp_gen);
        let spec = sig.to_gil_spec(global_env, self.name).unwrap();
        prog.add_only_spec(spec)
    }
}

pub(super) struct InnerPred<'tcx> {
    name: String,
    did: DefId,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> InnerPred<'tcx> {
    pub fn new(name: String, did: DefId, args: GenericArgsRef<'tcx>) -> Self {
        Self { name, did, args }
    }

    // TODO: Rewrite this awful awful code. Unfortunately, the POPL deadline demands we march forward
    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let mut temp_gen = TempGenerator::new();
        // let ctx = PredCtx::new_with_identity_args(global_env, &mut temp_gen, self.did);

        if global_env.prophecies_enabled() {
            let outer_term = EarlyBinder::bind(global_env.predicate(self.did).clone())
                .instantiate(global_env.tcx(), self.args);
            assert_eq!(outer_term.disjuncts.len(), 1);
            let assert = outer_term.disjuncts[0].1.clone();
            let asserts = assert.unstar();

            let mut call: Vec<_> = asserts
                .iter()
                .filter(|a| matches!(a.kind, gilsonite::AssertKind::Call(_)))
                .collect();
            assert_eq!(call.len(), 1);

            let gilsonite::AssertKind::Call(call) = &call.remove(0).kind else {
                unreachable!()
            };

            let mut term = EarlyBinder::bind(global_env.predicate(call.def_id).clone())
                .instantiate(global_env.tcx(), call.substs);
            assert_eq!(term.disjuncts.len(), 1);
            let assert = term.disjuncts[0].1.clone();

            let inner_asserts: Assert = assert
                .unstar()
                .into_iter()
                .filter(|a| !matches!(a.kind, gilsonite::AssertKind::ProphecyController { .. }))
                .cloned()
                .collect();

            term.disjuncts[0].1 = inner_asserts;

            let ref_mut = global_env.just_pred_name_with_args(call.def_id, call.substs);
            let ref_mut_inner = format!("{}$$inner", ref_mut);
            let mut ctx =
                PredCtx::new_with_args(global_env, &mut temp_gen, call.def_id, call.substs);
            let body = ctx.compile_predicate_body(term);
            let mut pred = ctx.finalize_pred(ref_mut_inner.clone(), body);

            pred.params.remove(0);
            pred.num_params -= 1;
            pred.ins.remove(0);
            pred.ins.iter_mut().for_each(|a| *a -= 1);
            pred.guard = None;
            prog.add_pred(pred);

            let base_name = global_env.just_pred_name_with_args(self.did, self.args);
            let body_term = global_env.predicate(self.did).clone();
            let mut ctx = PredCtx::new_with_args(global_env, &mut temp_gen, self.did, self.args);
            let body = ctx.compile_predicate_body(body_term);
            let body: Vec<_> = body
                .into_iter()
                .map(|def| {
                    let mut parts = def.unstar();
                    parts.iter_mut().for_each(|a| match a {
                        Assertion::Pred { name, params } if *name == ref_mut => {
                            *name = ref_mut_inner.clone();
                            params.remove(0);
                        }
                        _ => (),
                    });

                    parts.into_iter().reduce(Assertion::star).unwrap()
                })
                .collect();

            let mut pred = ctx.finalize_pred(base_name, body);
            pred.name = format!("{}$$inner", pred.name);
            pred.guard = None;
            pred.params.remove(0);
            pred.num_params -= 1;
            pred.ins.remove(0);
            pred.ins.iter_mut().for_each(|a| *a -= 1);

            prog.add_pred(pred);
            return;
        }

        let ctx = PredCtx::new_with_args(global_env, &mut temp_gen, self.did, self.args);

        let mut gil_pred = ctx.compile_concrete();
        // if global_env.prophecies_enabled() {
        //     fatal!(
        //         global_env,
        //         "InnerPred currently doesn't support prophecies {gil_pred}"
        //     );
        // }
        gil_pred.name = self.name;
        gil_pred.params.remove(0);
        gil_pred.num_params -= 1;
        gil_pred.ins.remove(0);
        gil_pred.ins.iter_mut().for_each(|a| *a -= 1);
        if std::mem::take(&mut gil_pred.guard).is_none() {
            // fatal!(global_env, "InnerPred for something that is not a borrow {:?}", self.did)
        }
        prog.add_pred(gil_pred);
    }
}

pub(super) enum AutoItem<'tcx> {
    MonoSpec(MonoSpec<'tcx>),
    ParamPred(ParamEnv<'tcx>, Instance<'tcx>),
    MonoPred(ParamEnv<'tcx>, Instance<'tcx>),
    InnerPred(InnerPred<'tcx>),
}

impl<'tcx> AutoItem<'tcx> {
    pub fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        match self {
            Self::MonoSpec(mono_spec) => mono_spec.add_to_prog(prog, global_env),
            Self::InnerPred(inner_pred) => inner_pred.add_to_prog(prog, global_env),
            Self::ParamPred(param_env, instance) => {
                let temp_gen = &mut temp_gen::TempGenerator::new();
                let pred = PredCtx::new(
                    global_env,
                    temp_gen,
                    param_env,
                    instance.def_id(),
                    instance.args,
                )
                .compile_abstract();
                prog.add_pred(pred);
            }
            Self::MonoPred(param_env, instance) => {
                // Otherwise, we just compile the predicate
                log::trace!(
                    "About to monomorphize predicate : {:?}",
                    global_env.just_pred_name_instance(instance)
                );
                if crate::utils::attrs::is_abstract_predicate(instance.def_id(), global_env.tcx()) {
                    let pred = PredCtx::new(
                        global_env,
                        &mut temp_gen::TempGenerator::new(),
                        param_env,
                        instance.def_id(),
                        instance.args,
                    )
                    .compile_abstract();
                    prog.add_pred(pred);
                } else if crate::utils::attrs::is_predicate(instance.def_id(), global_env.tcx()) {
                    let pred = PredCtx::new(
                        global_env,
                        &mut temp_gen::TempGenerator::new(),
                        param_env,
                        instance.def_id(),
                        instance.args,
                    )
                    .compile_concrete();
                    // HACK clean up when "AutoItem" is fixed
                    // if is_borrow(instance.def_id(), global_env.tcx()) {
                    //     global_env.inner_pred(pred.name.clone());
                    // };
                    prog.add_pred(pred);
                } else {
                    fatal!(
                        global_env,
                        "MonoPred but I don't know what it is? {:?}, {:?}",
                        instance.def_id(),
                        global_env.just_pred_name_instance(instance)
                    )
                }
            }
        }
    }
}

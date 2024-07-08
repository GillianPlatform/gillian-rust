use rustc_middle::ty::ParamEnv;

use crate::logic::PredCtx;
use crate::signature::build_signature;
use crate::temp_gen::TempGenerator;
use crate::utils::attrs::is_borrow;
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

    // Possibly duplicated compilation if the outer predicate
    // is already generated but it's fine
    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        if global_env.prophecies_enabled() {
            fatal!(global_env, "InnerPred to wait for prophecies")
        }
        let mut temp_gen = TempGenerator::new();
        let ctx = PredCtx::new_with_args(global_env, &mut temp_gen, self.did, self.args);
        let mut gil_pred = ctx.compile_concrete();
        if let None = std::mem::take(&mut gil_pred.guard) {
            fatal!(global_env, "InnerPred for something that is not a borrow")
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
                    // prog.add_pred(pred);
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

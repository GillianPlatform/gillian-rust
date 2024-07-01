use rustc_middle::ty::ParamEnv;

use crate::codegen::typ_encoding::type_param_name;
use crate::logic::{core_preds, param_collector, PredCtx};
use crate::signature::build_signature;
use crate::temp_gen::TempGenerator;
use crate::utils::attrs::is_borrow;
use crate::{prelude::*, temp_gen};

pub(super) struct MonoSpec<'tcx> {
    name: String,
    did: DefId,
    param_env: ParamEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> From<MonoSpec<'tcx>> for AutoItem<'tcx> {
    fn from(value: MonoSpec<'tcx>) -> Self {
        Self::MonoSpec(value)
    }
}

impl<'tcx> MonoSpec<'tcx> {
    pub fn new(
        name: String,
        did: DefId,
        param_env: ParamEnv<'tcx>,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        Self {
            name,
            did,
            param_env,
            args,
        }
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let mut temp_gen = TempGenerator::new();
        let sig = build_signature(global_env, self.did, self.args, &mut temp_gen);
        let spec = sig.to_gil_spec(global_env, self.name).unwrap();
        prog.add_only_spec(spec)
    }
}

pub(super) struct PcyAutoUpdate<'tcx> {
    param_env: ParamEnv<'tcx>,
    updater_name: String,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> PcyAutoUpdate<'tcx> {
    pub fn new(
        param_env: ParamEnv<'tcx>,
        updater_name: String,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        Self {
            param_env,
            updater_name,
            args,
        }
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let mutref = Expr::pvar("mut_ref");
        let mutref_ty = self.args[0]
            .as_type()
            .expect("Invalid substs for prophecy_auto_update?");
        let inner_ty = ty_utils::mut_ref_inner(mutref_ty)
            .expect("Calling prophecy_auto_update on something that isn't a mutref");
        let pointee = Expr::lvar("#pointee");
        let new_repr = "#new_repr".to_owned();
        let pointer = mutref.clone().lnth(0);
        let pcy = mutref.lnth(1);
        let value_cp =
            core_preds::value(pointer, global_env.encode_type(inner_ty), pointee.clone());
        let (own_pred_name, _, instance_args) =
            global_env.get_own_pred_for2(self.param_env, inner_ty);
        let collected_params = param_collector::collect_params_on_args(instance_args);
        let ty_params = collected_params
            .parameters
            .iter()
            .map(|ty| global_env.encode_param_ty(*ty).into());
        let own_pred_call = Assertion::Pred {
            name: own_pred_name,
            params: ty_params
                .chain([pointee, Expr::LVar(new_repr.clone())])
                .collect(),
        };
        let asrt_cmd = Cmd::slcmd(SLCmd::SepAssert {
            assertion: value_cp.star(own_pred_call),
            existentials: vec![new_repr.clone()],
        });
        let assign = Cmd::Action {
            variable: "u".to_owned(),
            action_name: crate::codegen::memory::action_names::PCY_ASSIGN.to_string(),
            parameters: vec![pcy.clone(), Expr::LVar(new_repr)],
        };
        let mut params = Vec::with_capacity(collected_params.parameters.len() + 2);
        params.push("pLft_a".to_owned());
        for ty_param in collected_params.parameters {
            let name = type_param_name(ty_param.index, ty_param.name);
            params.push(name);
        }
        params.push("mut_ref".to_owned());
        let proc = Proc {
            name: self.updater_name,
            body: vec![
                asrt_cmd.into(),
                assign.into(),
                Cmd::Assignment {
                    variable: "ret".into(),
                    assigned_expr: vec![].into(),
                }
                .into(),
                Cmd::ReturnNormal.into(),
            ],
            spec: None,
            params,
        };
        prog.add_proc(proc);
    }
}

impl<'tcx> From<PcyAutoUpdate<'tcx>> for AutoItem<'tcx> {
    fn from(value: PcyAutoUpdate<'tcx>) -> Self {
        Self::PcyAutoUpdate(value)
    }
}

/// Corresponds to a spec of the form
/// ```gil
///  spec [resolver_name](lft, T, U, mut_ref):
///     { [&'lft mut TY<T, U>]::own(mut_ref, (#current, #future)) }
///     { <#current == #future> }
/// ```
/// where `mut_ref_own_name` corresponds to `[&'lft mut TY<T, U>]::own`
pub(super) struct Resolver<'tcx> {
    param_env: ParamEnv<'tcx>,
    resolver_name: String,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> Resolver<'tcx> {
    pub fn new(
        param_env: ParamEnv<'tcx>,
        resolver_name: String,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        Self {
            param_env,
            resolver_name,
            args,
        }
    }

    pub fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let current = Expr::LVar("#current".to_string());
        let future = Expr::LVar("#future".to_string());
        let mut_ref = "mut_ref".to_string();
        let ty = global_env.tcx().erase_regions_ty(self.args.type_at(0));
        let (mut_ref_own_name, _, inner_subst) = global_env.get_own_pred_for2(self.param_env, ty);
        let inner_subst_params = param_collector::collect_params_on_args(inner_subst);
        let pred_params = inner_subst_params
            .parameters
            .into_iter()
            .map(|ty| type_param_name(ty.index, ty.name))
            .chain(std::iter::once(mut_ref));
        let pred_params: Vec<_> = std::iter::once(String::from("lft"))
            .chain(pred_params)
            .collect();
        let own_params = pred_params
            .clone()
            .into_iter()
            // .cloned()
            .map(Expr::PVar)
            .chain(std::iter::once(
                vec![current.clone(), future.clone()].into(),
            ))
            .collect();
        let pre = Assertion::Pred {
            name: mut_ref_own_name,
            params: own_params,
        };
        let resolved_observation =
            crate::logic::core_preds::observation(Expr::eq_expr(current, future));
        let posts = vec![resolved_observation];
        let spec = Spec {
            name: self.resolver_name,
            params: pred_params,
            sspecs: vec![SingleSpec {
                pre,
                posts,
                flag: Flag::Normal,
                trusted: true,
            }],
        };
        prog.add_only_spec(spec);
    }
}

pub(super) enum AutoItem<'tcx> {
    PcyAutoUpdate(PcyAutoUpdate<'tcx>),
    Resolver(Resolver<'tcx>),
    MonoSpec(MonoSpec<'tcx>),
    ParamPred(ParamEnv<'tcx>, Instance<'tcx>),
    MonoPred(ParamEnv<'tcx>, Instance<'tcx>),
}

impl<'tcx> From<Resolver<'tcx>> for AutoItem<'tcx> {
    fn from(resolver: Resolver<'tcx>) -> Self {
        Self::Resolver(resolver)
    }
}

impl<'tcx> AutoItem<'tcx> {
    pub fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        match self {
            Self::PcyAutoUpdate(pcy_auto_update) => pcy_auto_update.add_to_prog(prog, global_env),
            Self::Resolver(resolver) => resolver.add_to_prog(prog, global_env),
            Self::MonoSpec(mono_spec) => mono_spec.add_to_prog(prog, global_env),
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
                    if is_borrow(instance.def_id(), global_env.tcx()) {
                        global_env.inner_pred(pred.name.clone());
                    };
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

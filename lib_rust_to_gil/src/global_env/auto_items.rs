use rustc_middle::ty::ParamTy;

use crate::codegen::typ_encoding::type_param_name;
use crate::logic::{core_preds, param_collector, PredCtx};
use crate::{prelude::*, temp_gen};

pub(super) struct PcyAutoUpdate<'tcx> {
    updater_name: String,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> PcyAutoUpdate<'tcx> {
    pub fn new(updater_name: String, args: GenericArgsRef<'tcx>) -> Self {
        Self { updater_name, args }
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
        let (own_pred_name, instance_args) = global_env.get_own_pred_for(inner_ty);
        let collected_params = param_collector::collect_params_on_args(instance_args);
        let ty_params = collected_params
            .parameters
            .iter()
            .map(|ty| global_env.encode_type(*ty).into());
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

        let repr_ty = global_env.get_repr_ty_for(inner_ty).unwrap();
        let repr_ty = global_env.encode_type(repr_ty).into();
        let assign = Cmd::Action {
            variable: "u".to_owned(),
            action_name: crate::codegen::memory::action_names::PCY_ASSIGN.to_string(),
            parameters: vec![
                pcy.clone().lnth(0),
                pcy.lnth(1),
                repr_ty,
                Expr::LVar(new_repr),
            ],
        };
        let mut params = Vec::with_capacity(collected_params.parameters.len() + 2);
        params.push("pLft_a".to_owned());
        for ty_param in collected_params.parameters {
            let ParamTy { index, name } = crate::utils::ty::extract_param_ty(ty_param);
            let name = type_param_name(index, name);
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
    resolver_name: String,
    args: GenericArgsRef<'tcx>,
}

impl<'tcx> Resolver<'tcx> {
    pub fn new(resolver_name: String, args: GenericArgsRef<'tcx>) -> Self {
        Self {
            resolver_name,
            args,
        }
    }

    pub fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let current = Expr::LVar("#current".to_string());
        let future = Expr::LVar("#future".to_string());
        let mut_ref = "mut_ref".to_string();
        let ty = global_env.tcx().erase_regions_ty(self.args.type_at(0));
        let (mut_ref_own_name, inner_subst) = global_env.get_own_pred_for(ty);
        let inner_subst_params = param_collector::collect_params_on_args(inner_subst);
        let pred_params = inner_subst_params
            .parameters
            .into_iter()
            .map(|ty| {
                let TyKind::Param(ParamTy { index, name }) = *ty.kind() else {
                    panic!("unexpected parameter type??")
                };
                let name = name.to_string();
                type_param_name(index, Symbol::intern(&name))
            })
            .chain(std::iter::once(mut_ref));
        let pred_params = std::iter::once(String::from("lft")).chain(pred_params);
        let own_params = pred_params
            .clone()
            .map(Expr::PVar)
            .chain(std::iter::once(
                vec![current.clone(), future.clone()].into(),
            ))
            .collect();
        let pre = Assertion::Pred {
            name: mut_ref_own_name,
            params: own_params,
        };
        let resolved_observation = crate::logic::core_preds::observation(current.eq_f(future));
        let posts = vec![resolved_observation];
        let spec = Spec {
            name: self.resolver_name,
            params: pred_params.collect(),
            sspecs: vec![SingleSpec {
                pre,
                posts,
                flag: Flag::Normal,
            }],
        };
        prog.add_only_spec(spec);
    }
}

pub(super) enum AutoItem<'tcx> {
    PcyAutoUpdate(PcyAutoUpdate<'tcx>),
    Resolver(Resolver<'tcx>),
    ParamPred(Instance<'tcx>),
    MonoPred(Instance<'tcx>),
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
            Self::ParamPred(instance) => {
                let temp_gen = &mut temp_gen::TempGenerator::new();
                let pred = PredCtx::new(global_env, temp_gen, instance.def_id(), instance.args)
                    .compile_abstract();
                prog.add_pred(pred);
            }
            Self::MonoPred(instance) => {
                // This is the place where we create monomorphised items.
                log::trace!(
                    "About to monomorphize predicate : {:?}",
                    global_env.just_pred_name_instance(instance)
                );
                if crate::utils::attrs::is_abstract_predicate(instance.def_id(), global_env.tcx()) {
                    let pred = PredCtx::new(
                        global_env,
                        &mut temp_gen::TempGenerator::new(),
                        instance.def_id(),
                        instance.args,
                    )
                    .compile_abstract();
                    prog.add_pred(pred);
                } else if crate::utils::attrs::is_predicate(instance.def_id(), global_env.tcx()) {
                    let pred = PredCtx::new(
                        global_env,
                        &mut temp_gen::TempGenerator::new(),
                        instance.def_id(),
                        instance.args,
                    )
                    .compile_concrete();
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

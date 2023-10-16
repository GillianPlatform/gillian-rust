use rustc_middle::ty::ParamTy;

use crate::codegen::typ_encoding::type_param_name;
use crate::logic::builtins::LogicStubs;
use crate::logic::traits::TraitSolver;
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
        let repr_ty = global_env.get_repr_ty_for(inner_ty);
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
        let (mut_ref_own_name, inner_subst) = global_env.get_own_pred_for(self.args.type_at(0));
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

// Hopefully in the future, we can do multi-crate compilation that keeps track of logic, like Creusot.
// At which point, this code will yeet.
// This corresponds to the predicate [&mut inner_ty].own
struct MutRefOwn<'tcx> {
    pred_name: String,
    inner_ty: Ty<'tcx>,
}

impl<'tcx> MutRefOwn<'tcx> {
    fn of_instance(instance: Instance<'tcx>, global_env: &GlobalEnv<'tcx>) -> Option<Self> {
        let stub = LogicStubs::of_def_id(instance.def_id(), global_env.tcx());
        if let Some(LogicStubs::MutRefOwnPred) = stub {
            // If the first argument is a region, then we have
            let ty = instance.args.type_at(1);
            let name = global_env.just_pred_name_instance(instance);
            return Some(Self {
                pred_name: name,
                inner_ty: ty,
            });
        }
        None
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let own = global_env.get_own_def_did();

        let Self {
            pred_name,
            inner_ty,
        } = self;

        let old_subst = global_env.tcx().mk_args(&[(inner_ty).into()]);
        let inner_resolved = global_env.resolve_predicate(own, old_subst);
        let generic_params = std::iter::once(("lft".to_string(), None)).chain(
            inner_resolved.1.iter().enumerate().map(|(i, k)| {
                let name = k.to_string();
                let name = type_param_name(i.try_into().unwrap(), Symbol::intern(&name));
                (name, None)
            }),
        );
        let mut params: Vec<_> = generic_params
            .clone()
            .chain([("self".to_string(), Some(Type::ListType))])
            .collect();
        let mut num_params = inner_resolved.1.len() + 2;

        let slf: Expr = Expr::PVar("self".to_string());
        let (definitions, guard) = if global_env.config.prophecies {
            params.push(("model".to_string(), None));
            num_params += 1;
            let ptr = Expr::LVar("#ptr".to_string());
            let pcy = Expr::LVar("#pcy".to_string());
            let full_pcy: Expr = [pcy, vec![].into()].into();
            let self_deconstr_formula = slf.clone().eq_f([ptr, full_pcy.clone()]);
            let future = Expr::LVar("#future".to_string());
            let current = Expr::LVar("#current".to_string());
            let model = Expr::PVar("model".to_string());
            let model_deconstr_formula = model.clone().eq_f([current.clone(), future.clone()]);
            let repr_ty_id = global_env.get_repr_ty_did();
            let model_type = global_env.resolve_associated_type(repr_ty_id, inner_ty);
            let encoded_model_type = global_env.encode_type(model_type);
            let pcy_value = crate::logic::core_preds::pcy_value(
                full_pcy.clone(),
                encoded_model_type.clone(),
                future,
            );
            let observer =
                crate::logic::core_preds::observer(full_pcy, encoded_model_type, current);
            let ref_mut_inner_def_did = global_env.get_ref_mut_inner_did();
            let (ref_mut_inner_pred_name, _) =
                global_env.resolve_predicate(ref_mut_inner_def_did, old_subst);
            let ref_mut_inner_call = Assertion::Pred {
                name: ref_mut_inner_pred_name,
                params: generic_params
                    .map(|(ty, _)| Expr::PVar(ty))
                    .chain(std::iter::once(slf))
                    .collect(),
            };
            let definition = self_deconstr_formula
                .into_asrt()
                .star(model_deconstr_formula.into_asrt())
                .star(pcy_value)
                .star(observer)
                .star(ref_mut_inner_call);
            (vec![definition], None)
        } else {
            let slf = Expr::PVar("self".to_string());
            let v = Expr::LVar("#v".to_string());
            let pt =
                crate::logic::core_preds::value(slf, global_env.encode_type(inner_ty), v.clone());
            let params = generic_params
                .skip(1)
                .map(|(ty, _)| Expr::PVar(ty))
                .chain(std::iter::once(v))
                .collect();
            let own = Assertion::Pred {
                name: inner_resolved.0,
                params,
            };
            let guard = crate::logic::core_preds::alive_lft(Expr::PVar("lft".to_string()));
            (vec![pt.star(own)], Some(guard))
        };

        let pred = Pred {
            name: pred_name.clone(),
            num_params,
            params,
            ins: (0..num_params - (global_env.config.prophecies as usize)).collect(),
            definitions,
            pure: false,
            abstract_: false,
            facts: vec![],
            guard,
        };
        prog.add_pred(pred);
    }
}

struct OptionOwn<'tcx> {
    pred_name: String,
    ty: Ty<'tcx>,
}

impl<'tcx> OptionOwn<'tcx> {
    fn of_instance(instance: Instance<'tcx>, global_env: &GlobalEnv<'tcx>) -> Option<Self> {
        let stub = LogicStubs::of_def_id(instance.def_id(), global_env.tcx());
        if let Some(LogicStubs::OptionOwnPred) = stub {
            // If the first argument is a region, then we have
            let ty = instance.args.type_at(0);
            let name = global_env.just_pred_name_instance(instance);
            return Some(Self {
                pred_name: name,
                ty,
            });
        }
        None
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        if global_env.config.prophecies {
            fatal!(
                global_env,
                "Option::own not yet implemented with prophecies"
            )
        }
        let slf = Expr::PVar("self".into());
        // first_def is `self == [ 0i, [] ]`
        let first_def = slf
            .clone()
            .eq_f([0.into(), Expr::EList(vec![])])
            .into_asrt();
        let second_def = {
            let lvar_x = Expr::LVar("#x".into());
            let eq = slf
                .eq_f([1.into(), Expr::EList(vec![lvar_x.clone()])])
                .into_asrt();
            let own = global_env.get_own_pred_for(self.ty);
            let ty_params = param_collector::collect_params_on_args(own.1);
            let mut params =
                Vec::with_capacity(ty_params.parameters.len() + (ty_params.regions as usize) + 1);
            if ty_params.regions {
                params.push(Expr::PVar("lft".into()));
            }
            for ty in ty_params.parameters {
                params.push(global_env.encode_type(ty).into())
            }
            params.push(lvar_x);
            let own_call = Assertion::Pred {
                name: own.0,
                params,
            };
            eq.star(own_call)
        };
        let ty_params = crate::logic::param_collector::collect_params(self.ty)
            .with_consider_arguments([self.ty].into_iter());
        let mut params: Vec<(String, Option<_>)> =
            Vec::with_capacity(ty_params.parameters.len() + (ty_params.regions as usize) + 1);
        if ty_params.regions {
            params.push(("lft".into(), None));
        }
        for tyarg in ty_params.parameters {
            let tyarg = match *tyarg.kind() {
                TyKind::Param(ParamTy { index, name }) => type_param_name(index, name),
                _ => fatal!(global_env, "unreachable!"),
            };
            params.push((tyarg, None));
        }
        params.push(("self".into(), None));
        let pred = gillian::gil::Pred {
            name: self.pred_name,
            num_params: params.len(),
            ins: (0..params.len()).collect(),
            params,
            definitions: vec![first_def, second_def],
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: None,
        };
        prog.add_pred(pred);
    }
}

pub struct MutRefInner<'tcx> {
    pred_name: String,
    inner_ty: Ty<'tcx>,
}

impl<'tcx> MutRefInner<'tcx> {
    fn of_instance(instance: Instance<'tcx>, global_env: &GlobalEnv<'tcx>) -> Option<Self> {
        let stub = LogicStubs::of_def_id(instance.def_id(), global_env.tcx());
        if let Some(LogicStubs::RefMutInner) = stub {
            // If the first argument is a region, then we have
            let ty = instance.args.type_at(0);
            let name = global_env.just_pred_name_instance(instance);
            return Some(Self {
                pred_name: name,
                inner_ty: ty,
            });
        }
        None
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        if !global_env.config.prophecies {
            fatal!(
                global_env,
                "Please use --prophecies to use prophetic features"
            )
        }
        let own = global_env.get_own_pred_for(self.inner_ty);
        let repr_ty = global_env.get_repr_ty_for(self.inner_ty);
        let slf = Expr::PVar("self".to_string());
        let pointer = slf.clone().lnth(0);
        let pointee = Expr::LVar("#value".to_string());
        let repr = Expr::LVar("#repr".to_string());
        let points_to = core_preds::value(
            pointer,
            global_env.encode_type(self.inner_ty),
            pointee.clone(),
        );
        let controller =
            core_preds::controller(slf.lnth(1), global_env.encode_type(repr_ty), repr.clone());
        let params = own.1.iter().enumerate().map(|(i, k)| {
            let name = k.to_string();
            type_param_name(i.try_into().unwrap(), Symbol::intern(&name))
        });
        let own_call = Assertion::Pred {
            name: own.0,
            params: params
                .clone()
                .map(Expr::PVar)
                .chain([pointee, repr])
                .collect(),
        };
        let definitions = vec![points_to.star(controller).star(own_call)];
        let all_params: Vec<_> = std::iter::once("lft".to_string())
            .chain(params)
            .chain(std::iter::once("self".to_string()))
            .map(|x| (x, None))
            .collect();
        let pred = Pred {
            name: self.pred_name,
            num_params: all_params.len(),
            ins: (0..all_params.len()).collect(),
            params: all_params,
            definitions,
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: Some(core_preds::alive_lft(Expr::PVar("lft".to_string()))),
        };
        prog.add_pred(pred);
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
                // Some of them (from gilogic, because we don't do multi-crate yet) we have to manually shim.
                // This is annoying but fixable long term.
                // Some others we just compile monomorphized.
                if let Some(mut_ref_own) = MutRefOwn::of_instance(instance, global_env) {
                    mut_ref_own.add_to_prog(prog, global_env);
                    return;
                }
                if let Some(option_own) = OptionOwn::of_instance(instance, global_env) {
                    option_own.add_to_prog(prog, global_env);
                    return;
                }
                if let Some(mut_ref_inner) = MutRefInner::of_instance(instance, global_env) {
                    mut_ref_inner.add_to_prog(prog, global_env);
                    return;
                }
                fatal!(global_env, "Unsupported MonoPred! {:?}", instance)
            }
        }
    }
}

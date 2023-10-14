use crate::codegen::typ_encoding::type_param_name;
use crate::logic::builtins::Stubs;
use crate::logic::traits::TraitSolver;
use crate::logic::PredCtx;
use crate::{prelude::*, temp_gen};
/// Corresponds to a spec of the form
/// ```gil
///  spec [resolver_name](lft, T, U, mut_ref):
///     { [&'lft mut TY<T, U>]::own(mut_ref, (#current, #future)) }
///     { <#current == #future> }
/// ```
/// where `mut_ref_own_name` corresponds to `[&'lft mut TY<T, U>]::own`
pub(super) struct Resolver<'tcx> {
    resolver_name: String,
    mut_ref_own_name: String,
    inner_subst: GenericArgsRef<'tcx>,
}

impl<'tcx> Resolver<'tcx> {
    pub fn new(
        resolver_name: String,
        mut_ref_own_name: String,
        inner_subst: GenericArgsRef<'tcx>,
    ) -> Self {
        Self {
            resolver_name,
            mut_ref_own_name,
            inner_subst,
        }
    }

    pub fn add_to_prog(self, prog: &mut Prog) {
        let current = Expr::LVar("#current".to_string());
        let future = Expr::LVar("#future".to_string());
        let mut_ref = "mut_ref".to_string();
        let pred_params = self
            .inner_subst
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let name = k.to_string();
                type_param_name(i.try_into().unwrap(), Symbol::intern(&name))
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
            name: self.mut_ref_own_name,
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
pub(super) struct MutRefOwn<'tcx> {
    pred_name: String,
    inner_ty: Ty<'tcx>,
}

impl<'tcx> MutRefOwn<'tcx> {
    fn of_instance(instance: Instance<'tcx>, global_env: &GlobalEnv<'tcx>) -> Option<Self> {
        let stub = Stubs::of_def_id(instance.def_id(), global_env.tcx());
        if let Some(Stubs::MutRefOwnPred) = stub {
            // If the first argument is a region, then we have
            let ty = instance.args.type_at(1);
            log::debug!("TY? {:?}", ty);
            let name = global_env.just_pred_name_instance(instance);
            return Some(Self {
                pred_name: name,
                inner_ty: ty,
            });
        }
        None
    }

    fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        let symbol = if global_env.config.prophecies {
            Symbol::intern("gillian::pcy::ownable::own")
        } else {
            Symbol::intern("gillian::ownable::own")
        };

        let own = global_env
            .tcx()
            .get_diagnostic_item(symbol)
            .expect("Could not find gilogic::Ownable");

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
            let repr_ty_id = global_env
                .tcx()
                .get_diagnostic_item(Symbol::intern("gillian::pcy::ownable::representation_ty"))
                .expect("Couldn't find gillian::ownable::representation_ty");
            let model_type = global_env.resolve_associated_type(repr_ty_id, inner_ty);
            let encoded_model_type = global_env.encode_type(model_type);
            let pcy_value = crate::logic::core_preds::pcy_value(
                full_pcy.clone(),
                encoded_model_type.clone(),
                future,
            );
            let observer =
                crate::logic::core_preds::observer(full_pcy, encoded_model_type, current);
            let ref_mut_inner_def_did = global_env
                .tcx()
                .get_diagnostic_item(Symbol::intern("gillian::pcy::ownable::ref_mut_inner"))
                .expect("Couldn't find gillian::pcy::ownable::ref_mut_inner");
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

pub(super) enum AutoItem<'tcx> {
    Resolver(Resolver<'tcx>),
    ParamPred(Instance<'tcx>),
    MonoPred(Instance<'tcx>),
}

impl<'tcx> AutoItem<'tcx> {
    pub fn add_to_prog(self, prog: &mut Prog, global_env: &mut GlobalEnv<'tcx>) {
        match self {
            Self::Resolver(resolver) => resolver.add_to_prog(prog),
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
                log::warn!(
                    "Should be adding {:?} to program, substs is: {:?}",
                    global_env.just_pred_name_instance(instance),
                    instance.args,
                );
            }
        }
    }
}

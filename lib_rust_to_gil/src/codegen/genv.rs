use crate::logic::core_preds::{self, alive_lft};
use crate::prelude::*;
use crate::{config::Config, logic::traits::TraitSolver};
use rustc_data_structures::sync::HashMapExt;
use rustc_middle::ty::{AdtDef, GenericArgsRef, ReprOptions};
use serde_json::{self, json};
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use super::typ_encoding::type_param_name;

struct QueueOnce<K> {
    queue: VecDeque<K>,
    done: HashSet<K>,
}

impl<K> Default for QueueOnce<K> {
    fn default() -> Self {
        Self {
            queue: Default::default(),
            done: Default::default(),
        }
    }
}

impl<K> QueueOnce<K>
where
    K: Eq + Hash + Clone,
{
    fn push(&mut self, v: K) {
        if !(self.done.contains(&v) || self.queue.contains(&v)) {
            self.queue.push_back(v);
        }
    }

    fn pop(&mut self) -> Option<K> {
        let elem = self.queue.pop_front();
        if let Some(elem) = &elem {
            self.done.insert(elem.clone());
        }
        elem
    }
}

pub struct GlobalEnv<'tcx> {
    // Things that are global to compilation
    tcx: TyCtxt<'tcx>,
    pub config: Config,
    /// The types that should be encoded for the GIL global env
    adt_queue: QueueOnce<AdtDef<'tcx>>,
    mut_ref_owns: HashMap<Ty<'tcx>, String>,
    mut_ref_inners: HashMap<Ty<'tcx>, (String, Ty<'tcx>)>,
    mut_ref_resolvers: HashMap<Ty<'tcx>, (String, String, GenericArgsRef<'tcx>)>,
    // MUTREF_TY -> (RESOLVER_NAME, MUTREF_OWN_NAME, INNER_SUBST)
    inner_preds: HashMap<String, String>,
    // Borrow preds for which an $$inner version should be derived.
}

impl<'tcx> HasTyCtxt<'tcx> for GlobalEnv<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

pub trait HasGlobalEnv<'tcx> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx>;

    fn global_env(&self) -> &GlobalEnv<'tcx>;
}

impl<'tcx> HasGlobalEnv<'tcx> for GlobalEnv<'tcx> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx> {
        self
    }

    fn global_env(&self) -> &GlobalEnv<'tcx> {
        self
    }
}

impl<'tcx> TypeEncoder<'tcx> for GlobalEnv<'tcx> {}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, config: Config) -> Self {
        Self {
            config,
            tcx,
            adt_queue: Default::default(),
            mut_ref_owns: Default::default(),
            mut_ref_inners: Default::default(),
            mut_ref_resolvers: Default::default(),
            inner_preds: Default::default(),
        }
    }

    pub fn pred_name_for(&self, did: DefId, args: GenericArgsRef<'tcx>) -> String {
        self.tcx().def_path_str_with_args(did, args)
    }

    pub fn pred_name_for_instance(&self, instance: Instance<'tcx>) -> String {
        self.pred_name_for(instance.def_id(), instance.args)
    }

    pub fn inner_pred(&mut self, pred: String) -> String {
        let name = pred.clone() + "$$inner";
        self.inner_preds.insert_same(pred, name.clone());
        name
    }

    pub fn get_own_pred_for(&self, ty: Ty<'tcx>) -> Instance<'tcx> {
        let symbol = crate::logic::builtins::Stubs::OwnPred.symbol(self.config.prophecies);
        let general_own = self
            .tcx()
            .get_diagnostic_item(symbol)
            .expect("Could not find gilogic::Ownable");
        let subst = self.tcx().mk_args(&[ty.into()]);
        self.resolve_candidate(general_own, subst)
    }

    pub fn add_resolver(&mut self, mutref_ty: Ty<'tcx>) -> (String, GenericArgsRef<'tcx>) {
        let inner_ty = crate::utils::ty::mut_ref_inner(mutref_ty).unwrap();
        let instance = self.get_own_pred_for(inner_ty);
        let mutref_own_name = format!("<{} as gilogic::prophecies::Ownable>::own", mutref_ty);
        let name = format!("{}::$resolver", mutref_ty);
        self.encode_type(mutref_ty); // Encoding is a way to make sure that the type is recorded in the env.
        self.mut_ref_resolvers
            .insert(mutref_ty, (name.clone(), mutref_own_name, instance.args));
        (name, instance.args)
    }

    pub fn add_mut_ref_own(&mut self, ty: Ty<'tcx>) -> String {
        self.mut_ref_owns
            .entry(ty)
            .or_insert_with(|| {
                if self.config.prophecies {
                    format!("<{} as gilogic::prophecies::Ownable>::own", ty)
                } else {
                    format!("<{} as gilogic::Ownable>::own", ty)
                }
            })
            .clone()
    }

    pub fn add_resolvers_to_prog(&mut self, prog: &mut Prog) {
        if !self.config.prophecies {
            return;
        }
        let mut_ref_resolvers = std::mem::take(&mut self.mut_ref_resolvers);
        for (_, (name, own_name, subst)) in mut_ref_resolvers {
            let current = Expr::LVar("#current".to_string());
            let future = Expr::LVar("#future".to_string());
            let mut_ref = "mut_ref".to_string();
            let pred_params = subst
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
                name: own_name,
                params: own_params,
            };
            let resolved_observation = core_preds::observation(current.eq_f(future));
            let posts = vec![resolved_observation];
            let spec = Spec {
                name,
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

    // Has to be called after add_mut_ref_owns_to_prog,
    // Since it's the one adding the right things to the map.
    // In the map, the type used as is the *inner* type, not the mutable reference.
    fn add_mut_ref_inners_to_prog(&mut self, prog: &mut Prog) {
        if !self.config.prophecies {
            return;
        }
        let mut_ref_inners = std::mem::take(&mut self.mut_ref_inners);
        for (inner_ty, (name, repr_ty)) in mut_ref_inners.iter() {
            // Some of this code already exists in the next function, it could somehow be factored out.
            let symbol = Symbol::intern("gillian::pcy::ownable::own");
            let own = self
                .tcx()
                .get_diagnostic_item(symbol)
                .expect("Could not find gilogic::Ownable");
            let subst = self.tcx().mk_args(&[(*inner_ty).into()]);
            let instance = self.resolve_candidate(own, subst);
            let slf = Expr::PVar("self".to_string());
            let pointer = slf.clone().lnth(0);
            let pointee = Expr::LVar("#value".to_string());
            let repr = Expr::LVar("#repr".to_string());
            let points_to =
                core_preds::value(pointer, self.encode_type(*inner_ty), pointee.clone());
            let controller =
                core_preds::controller(slf.lnth(1), self.encode_type(*repr_ty), repr.clone());
            let params = instance.args.iter().enumerate().map(|(i, k)| {
                let name = k.to_string();
                type_param_name(i.try_into().unwrap(), Symbol::intern(&name))
            });
            let own_call = Assertion::Pred {
                name: self.pred_name_for_instance(instance),
                params: params
                    .clone()
                    .map(Expr::PVar)
                    .chain([pointee, repr].into_iter())
                    .collect(),
            };
            let definitions = vec![points_to.star(controller).star(own_call)];
            let all_params: Vec<_> = std::iter::once("lft".to_string())
                .chain(params)
                .chain(std::iter::once("self".to_string()))
                .map(|x| (x, None))
                .collect();
            let pred = Pred {
                name: name.to_string(),
                num_params: all_params.len(),
                ins: (0..all_params.len()).collect(),
                params: all_params,
                definitions,
                pure: false,
                abstract_: false,
                facts: vec![],
                guard: Some(alive_lft(Expr::PVar("lft".to_string()))),
            };
            prog.add_pred(pred);
        }
    }

    fn add_mut_ref_owns_to_prog(&mut self, prog: &mut Prog) {
        let mut_ref_owns = std::mem::take(&mut self.mut_ref_owns);
        let symbol = if self.config.prophecies {
            Symbol::intern("gillian::pcy::ownable::own")
        } else {
            Symbol::intern("gillian::ownable::own")
        };

        let own = self
            .tcx()
            .get_diagnostic_item(symbol)
            .expect("Could not find gilogic::Ownable");
        for (ty, name) in mut_ref_owns.iter() {
            let inner_ty = match ty.kind() {
                TyKind::Ref(_, inner_ty, Mutability::Mut) => inner_ty,
                _ => unreachable!("Something that isn't a mutref was added to the mutrefs in genv"),
            };
            let old_subst = self.tcx().mk_args(&[(*inner_ty).into()]);

            let instance = self.resolve_candidate(own, old_subst);
            let generic_params = std::iter::once(("lft".to_string(), None)).chain(
                instance.args.iter().enumerate().map(|(i, k)| {
                    let name = k.to_string();
                    let name = type_param_name(i.try_into().unwrap(), Symbol::intern(&name));
                    (name, None)
                }),
            );
            let mut params: Vec<_> = generic_params
                .clone()
                .chain([("self".to_string(), Some(Type::ListType))].into_iter())
                .collect();
            let mut num_params = instance.args.len() + 2;

            let slf: Expr = Expr::PVar("self".to_string());
            let (definitions, guard) = if self.config.prophecies {
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
                let repr_ty_id = self
                    .tcx()
                    .get_diagnostic_item(Symbol::intern("gillian::pcy::ownable::representation_ty"))
                    .expect("Couldn't find gillian::ownable::representation_ty");
                let model_type = self.resolve_associated_type(repr_ty_id, *inner_ty);
                let encoded_model_type = self.encode_type(model_type);
                let pcy_value = crate::logic::core_preds::pcy_value(
                    full_pcy.clone(),
                    encoded_model_type.clone(),
                    future,
                );
                let observer =
                    crate::logic::core_preds::observer(full_pcy, encoded_model_type, current);
                let ref_mut_inner_pred_name = format!("<{} as Ownable>::ref_mut_inner", inner_ty);
                self.mut_ref_inners
                    .insert(*inner_ty, (ref_mut_inner_pred_name.clone(), model_type));
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
                    crate::logic::core_preds::value(slf, self.encode_type(*inner_ty), v.clone());
                let params = generic_params
                    .skip(1)
                    .map(|(ty, _)| Expr::PVar(ty))
                    .chain(std::iter::once(v))
                    .collect();
                let own = Assertion::Pred {
                    name: self.pred_name_for_instance(instance),
                    params,
                };
                let guard = crate::logic::core_preds::alive_lft(Expr::PVar("lft".to_string()));
                (vec![pt.star(own)], Some(guard))
            };

            let pred = Pred {
                name: name.clone(),
                num_params,
                params,
                ins: (0..num_params - (self.config.prophecies as usize)).collect(),
                definitions,
                pure: false,
                abstract_: false,
                facts: vec![],
                guard,
            };
            prog.add_pred(pred);
        }
    }

    fn add_inner_pred_to_prog(&mut self, prog: &mut Prog) {
        let inner_preds = std::mem::take(&mut self.inner_preds);
        for (pred, inner_pred) in inner_preds {
            let outer_pred = prog.preds.get(&pred).unwrap_or_else(|| {
                fatal!(
                    self,
                    "Cannot find {:?} to add its inner pred not found in genv",
                    pred
                )
            });
            if outer_pred.guard.is_none() {
                fatal!(
                    self,
                    "Adding inner pred for {:?}, which is not a borrow!",
                    pred
                )
            }
            let mut outer_pred: Pred = outer_pred.clone();
            outer_pred.guard = None;
            let zero_idx = outer_pred.ins.iter().position(|x| *x == 0).unwrap();
            outer_pred.ins.swap_remove(zero_idx);
            for in_ in outer_pred.ins.iter_mut() {
                *in_ -= 1;
            }
            outer_pred.num_params -= 1;
            outer_pred.params.remove(0);
            outer_pred.name = inner_pred;
            prog.add_pred(outer_pred);
        }
    }

    pub fn flush_remaining_defs_to_prog(&mut self, prog: &mut Prog) {
        self.add_resolvers_to_prog(prog);
        self.add_mut_ref_owns_to_prog(prog);
        self.add_mut_ref_inners_to_prog(prog);
        self.add_inner_pred_to_prog(prog);
    }

    fn serialize_repr(&self, repr: &ReprOptions) -> serde_json::Value {
        if repr.int.is_some() || repr.align.is_some() || repr.pack.is_some() {
            fatal!(
                self,
                "Cant handle this specific representations at the moment, only C"
            )
        };
        if repr.c() {
            "ReprC".into()
        } else {
            "ReprRust".into()
        }
    }

    // Panics if not called with an ADT
    fn serialize_adt_decl(&mut self, def: AdtDef<'tcx>) -> (String, serde_json::Value) {
        if def.is_struct() {
            let name = self.tcx.item_name(def.did()).to_string();
            let fields: Vec<serde_json::Value> = def
                .all_fields()
                .map(|field| {
                    let field_name = self.tcx.item_name(field.did).to_string();
                    let typ = self.tcx.type_of(field.did).instantiate_identity();
                    let typ = self.serialize_type(typ);
                    json!([field_name, typ])
                })
                .collect();
            let decl = json!(["Struct", self.serialize_repr(&def.repr()), fields]);
            (name, decl)
        } else if def.is_enum() {
            if def.is_variant_list_non_exhaustive() {
                fatal!(self, "Can't handle #[non_exhaustive] yet");
            }
            let name = self.tcx.item_name(def.did()).to_string();
            let variants: Vec<serde_json::Value> = def
                .variants()
                .iter()
                .map(|variant| {
                    let fields: Vec<serde_json::Value> = variant
                        .fields
                        .iter()
                        .map(|field| {
                            let typ = self.tcx.type_of(field.did).instantiate_identity();
                            self.serialize_type(typ)
                        })
                        .collect();
                    let name = self.tcx.item_name(variant.def_id).to_string();
                    json!([name, fields])
                })
                .collect();
            let decl = json!(["Enum", variants]);
            (name, decl)
        } else {
            fatal!(self, "Unions not handled yet, can't encode: {:#?}", def)
        }
    }

    pub fn register_adt(&mut self, def: AdtDef<'tcx>) {
        self.adt_queue.push(def);
    }

    // This takes a self, because it's the last thing that should be done with the global env.
    // After that, encoding any type might lead to compilation forgetting to include it in the
    // initialization data.
    pub fn serialized_adt_declarations(mut self) -> serde_json::Value {
        use serde_json::{Map, Value};
        let mut obj: Map<String, Value> = Map::new();
        while let Some(adt) = self.adt_queue.pop() {
            let (name, ser_decl) = self.serialize_adt_decl(adt);
            let previous_entry = obj.insert(name.clone(), ser_decl.clone());
            if let Some(previous_entry) = previous_entry {
                if previous_entry != ser_decl {
                    fatal!(
                        self,
                        "Encoded two different types with the same name {}: {}\nAND\n{}",
                        name,
                        previous_entry,
                        ser_decl
                    )
                }
            }
        }
        Value::Object(obj)
    }
}

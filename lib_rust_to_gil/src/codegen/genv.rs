use crate::prelude::*;
use crate::{config::Config, logic::traits::TraitSolver};
use rustc_middle::ty::{AdtDef, ReprOptions};
use serde_json::{self, json};
use std::collections::{HashMap, HashSet, VecDeque};

use super::typ_encoding::type_param_name;

pub struct GlobalEnv<'tcx> {
    // Things that are global to compilation
    tcx: TyCtxt<'tcx>,
    pub config: Config,
    /// The types that should be encoded for the GIL global env
    types_in_queue: VecDeque<AdtDef<'tcx>>,
    encoded_adts: HashSet<AdtDef<'tcx>>,
    mut_ref_owns: HashMap<Ty<'tcx>, String>,
    // Contains the type and the name of the created predicate.
}

impl<'tcx> HasTyCtxt<'tcx> for GlobalEnv<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> TypeEncoder<'tcx> for GlobalEnv<'tcx> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.add_adt(def);
    }

    fn adt_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, config: Config) -> Self {
        Self {
            config,
            tcx,
            types_in_queue: Default::default(),
            encoded_adts: Default::default(),
            mut_ref_owns: Default::default(),
        }
    }

    pub fn add_mut_ref_own(&mut self, ty: Ty<'tcx>) -> String {
        self.mut_ref_owns
            .entry(ty)
            .or_insert_with(|| format!("{}::mut_ref_own", ty))
            .clone()
    }

    pub fn add_mut_ref_owns_to_prog(&mut self, prog: &mut Prog) {
        for (ty, name) in self.mut_ref_owns.iter() {
            let symbol = if self.config.prophecies {
                Symbol::intern("gillian::pcy::ownable::own")
            } else {
                Symbol::intern("gillian::ownable::own")
            };

            let own = self
                .tcx()
                .get_diagnostic_item(symbol)
                .expect("Could not find gilogic::Ownable");
            let inner_ty = match ty.kind() {
                TyKind::Ref(_, inner_ty, Mutability::Mut) => inner_ty,
                _ => unreachable!("Something that isn't a mutref was added to the mutrefs in genv"),
            };
            let subst =
                self.tcx()
                    .intern_substs(rustc_middle::ty::subst::ty_slice_as_generic_args(&[
                        *inner_ty,
                    ]));

            let (_, subst) = self.resolve_candidate(own, subst);
            let generic_params = subst.iter().enumerate().map(|(i, k)| {
                let name = k.to_string();
                let name = type_param_name(i.try_into().unwrap(), Symbol::intern(&name));
                (name, None)
            });
            let mut params: Vec<_> = generic_params
                .chain([("ref".to_string(), Some(Type::ListType))].into_iter())
                .collect();
            let mut num_params = subst.len() + 1;

            if self.config.prophecies {
                params.push(("model".to_string(), None));
                num_params += 1;
            }

            let pred = Pred {
                name: name.clone(),
                num_params,
                params,
                ins: (0..num_params - 1).into_iter().collect(),
                definitions: vec![],
                pure: false,
                abstract_: true,
                facts: vec![],
            };
            prog.add_pred(pred);
        }
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
        self.encoded_adts.insert(def);
        if def.is_struct() {
            let name = self.tcx.item_name(def.did()).to_string();
            let fields: Vec<serde_json::Value> = def
                .all_fields()
                .map(|field| {
                    let field_name = self.tcx.item_name(field.did).to_string();
                    let typ = self.tcx.type_of(field.did);
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
                            let typ = self.tcx.type_of(field.did);
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

    pub fn add_adt(&mut self, def: AdtDef<'tcx>) {
        if !(self.encoded_adts.contains(&def) || self.types_in_queue.contains(&def)) {
            self.types_in_queue.push_back(def);
        }
    }

    // This takes a self, because it's the last thing that should be done with the global env.
    // After that, encoding any type might lead to compilation forgetting to include it in the
    // initialization data.
    pub fn serialized_adt_declarations(mut self) -> serde_json::Value {
        use serde_json::{Map, Value};
        let mut obj: Map<String, Value> = Map::new();
        while !self.types_in_queue.is_empty() {
            let ty = self.types_in_queue.pop_front().unwrap();
            let (name, ser_decl) = self.serialize_adt_decl(ty);
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

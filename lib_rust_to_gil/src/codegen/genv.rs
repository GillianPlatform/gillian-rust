use crate::prelude::*;
use rustc_middle::ty::{AdtDef, ReprOptions};
use serde_json::{self, json};
use std::collections::{HashSet, VecDeque};

pub struct GlobalEnv<'tcx> {
    /// The types that should be encoded for the GIL global env
    tcx: TyCtxt<'tcx>,
    types_in_queue: VecDeque<AdtDef<'tcx>>,
    encoded_adts: HashSet<AdtDef<'tcx>>,
}

impl<'tcx> CanFatal<'tcx> for GlobalEnv<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> TypeEncoder<'tcx> for GlobalEnv<'tcx> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.add_adt(def);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            types_in_queue: Default::default(),
            encoded_adts: Default::default(),
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

use crate::prelude::*;
use rustc_middle::ty::{AdtDef, ReprOptions};
use serde_json::{self, json};
use std::collections::{HashSet, VecDeque};

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum CustomRuntime<'tcx> {
    PtrPlus(Ty<'tcx>, String),
}

pub struct GlobalEnv<'tcx> {
    /// The types that should be encoded for the GIL global env
    tcx: TyCtxt<'tcx>,
    types_in_queue: VecDeque<Ty<'tcx>>,
    encoded_adts: HashSet<Ty<'tcx>>,
    runtime_to_encode: HashSet<CustomRuntime<'tcx>>,
}

impl<'tcx> CanFatal for GlobalEnv<'tcx> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

impl<'tcx> TypeEncoder<'tcx> for GlobalEnv<'tcx> {
    fn add_adt_to_genv(&mut self, ty: Ty<'tcx>) {
        self.add_adt(ty);
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
            runtime_to_encode: Default::default(),
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
    fn serialize_adt_decl(&mut self, ty: Ty<'tcx>) -> (String, serde_json::Value) {
        self.encoded_adts.insert(ty);
        match ty.kind() {
            TyKind::Adt(def, subst) if def.is_struct() => {
                let name = self.tcx.item_name(def.did()).to_string();
                let fields: Vec<serde_json::Value> = def
                    .all_fields()
                    .map(|field| {
                        let field_name = self.tcx.item_name(field.did).to_string();
                        let typ = self.serialize_type(field.ty(self.tcx, subst));
                        json!([field_name, typ])
                    })
                    .collect();
                let decl = json!(["Struct", self.serialize_repr(&def.repr()), fields]);
                (name, decl)
            }
            TyKind::Adt(def, subst) if def.is_enum() => {
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
                            .map(|field| self.serialize_type(field.ty(self.tcx, subst)))
                            .collect();
                        let name = self.tcx.item_name(variant.def_id).to_string();
                        json!([name, fields])
                    })
                    .collect();
                let decl = json!(["Enum", variants]);
                (name, decl)
            }
            _ => panic!(
                "This function should never be called with this type {:#?}",
                ty
            ),
        }
    }

    pub fn add_adt(&mut self, ty: Ty<'tcx>) {
        if !(self.encoded_adts.contains(&ty) || self.types_in_queue.contains(&ty)) {
            self.types_in_queue.push_back(ty);
        }
    }

    pub fn add_runtime(&mut self, r: CustomRuntime<'tcx>) {
        self.runtime_to_encode.insert(r);
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

    fn proc_of_custom_runtime(&mut self, r: CustomRuntime<'tcx>) -> Proc {
        match r {
            CustomRuntime::PtrPlus(ty, fname) => self.ptr_plus_impl(ty, fname),
        }
    }

    pub fn add_all_procs(&mut self, prog: &mut Prog) {
        let runtime = self.runtime_to_encode.clone();
        for r in runtime {
            prog.add_proc(self.proc_of_custom_runtime(r))
        }
    }
}

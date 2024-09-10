use super::auto_items::*;
use crate::config::{Config, GillianArgs};
use crate::logic::gilsonite::{self, GilsoniteBuilder, SpecTerm};
use crate::logic::traits::{resolve_candidate, ResolvedImpl};
use crate::logic::utils::get_thir;
use crate::metadata::{BinaryMetadata, Metadata};
use crate::utils::attrs::{
    get_attr, get_gillian_extract_lemma_name, get_gillian_spec_name, is_trusted,
};
use crate::{callbacks, prelude::*};
use indexmap::IndexMap;
use once_map::OnceMap;
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_hir::def_id::LocalDefId;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::{
    AdtDef, GenericArg, GenericArgKind, GenericArgs, GenericArgsRef, ParamEnv, ReprOptions,
};
use serde_json::{self, json};
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

pub(super) struct QueueOnce<K, V> {
    queue: VecDeque<(K, V)>,
    done: HashSet<K>,
}

impl<K, V> Default for QueueOnce<K, V> {
    fn default() -> Self {
        Self {
            queue: Default::default(),
            done: Default::default(),
        }
    }
}

impl<K, V> QueueOnce<K, V>
where
    K: Eq + Clone + Hash,
{
    fn contains(&self, k: &K) -> bool {
        self.done.contains(k) || self.queue.iter().any(|(kk, _)| k == kk)
    }

    fn push(&mut self, k: K, v: V) {
        if !self.contains(&k) {
            self.queue.push_back((k, v));
        }
    }

    fn mark_as_done(&mut self, k: K) {
        self.done.insert(k);
    }

    fn pop(&mut self) -> Option<(K, V)> {
        loop {
            match self.queue.pop_front() {
                None => return None,
                Some((k, v)) => {
                    if self.done.insert(k.clone()) {
                        return Some((k, v));
                    }
                }
            }
        }
    }
}

/// Things that are global to the compilation of a rust program for Gillian-Rust.
/// It contains 3 main queues (and some that should be converted into one of these)
/// corresponding to three stages of compilation:
/// 1) Item queue: A list of items that should be encoded. Encoding each one might generate other items to encode.
/// 2) GIL post-processing: A list of post-processing to operate at the GIL level on the created program.
/// 3) Global level: adt_queue. This is to be encoded into a GIL `init_data` json record at the very end of compilation.
///    After we have seen all the types that participate in execution.
pub struct GlobalEnv<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub config: Config,

    /// The types that should be encoded for the GIL global env
    pub(super) adt_queue: QueueOnce<AdtDef<'tcx>, ()>,

    pub(super) item_queue: QueueOnce<String, AutoItem<'tcx>>,
    // Borrow preds for which an $$inner version should be derived.
    pub(super) inner_preds: IndexMap<String, String>,

    // Mapping from item -> specification
    spec_map: HashMap<DefId, DefId>,

    gillian_items: GillianItems,

    /// Assertions & specifications from external dependencies
    metadata: Metadata<'tcx>,

    assertions: OnceMap<DefId, Box<gilsonite::Predicate<'tcx>>>,

    spec_terms: OnceMap<DefId, Box<Option<gilsonite::SpecTerm<'tcx>>>>,

    bodies: OnceMap<LocalDefId, Box<BodyWithBorrowckFacts<'tcx>>>,
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
        // A few things are already implemented in GIL directly.
        let item_queue = QueueOnce::default();
        let gillian_items = local_gillian_items(tcx);
        let mut spec_map = Self::build_gillian_maps(tcx, &gillian_items);

        let metadata = Metadata::load(tcx, &config.extern_paths);

        // The spec map is extended with the spec maps of the dependencies.
        metadata.spec_map().iter().for_each(|(k, v)| {
            spec_map.insert(*k, *v);
        });

        // TODO: Import extract lemmas from dependencies?

        Self {
            config,
            tcx,
            adt_queue: Default::default(),
            item_queue,
            spec_map,
            metadata,
            gillian_items,
            inner_preds: Default::default(),
            bodies: Default::default(),
            assertions: Default::default(),
            spec_terms: Default::default(),
        }
    }

    fn build_gillian_maps(
        tcx: TyCtxt<'tcx>,
        gillian_items: &GillianItems,
    ) -> HashMap<DefId, DefId> {
        let mut spec_map = HashMap::new();
        // panic!();
        // eprintln!("{:?}", gillian_items.symbol_to_id);
        for item in tcx.hir().body_owners() {
            if let Some(nm) = get_gillian_spec_name(item.into(), tcx) {
                let spec = tcx
                    .get_diagnostic_item(nm)
                    .or_else(|| gillian_items.symbol_to_id.get(&nm).cloned())
                    .expect("Cannot find specification while building spec map");
                spec_map.insert(item.to_def_id(), spec);
            }
        }
        spec_map
    }

    pub fn prophecies_enabled(&self) -> bool {
        self.config.prophecies
    }

    pub fn just_pred_name_with_args(&self, did: DefId, args: GenericArgsRef<'tcx>) -> String {
        let args: Vec<GenericArg> = args
            .iter()
            .map(|k| match k.unpack() {
                GenericArgKind::Lifetime(..) => self.tcx().lifetimes.re_erased.into(),
                _ => k,
            })
            .collect();
        let args = self.tcx().mk_args(&args);
        self.tcx.def_path_str_with_args(did, args)
    }

    pub fn just_pred_name(&self, did: DefId) -> String {
        let args = GenericArgs::identity_for_item(self.tcx, did);
        self.just_pred_name_with_args(did, args)
    }

    pub fn just_pred_name_instance(&self, instance: Instance<'tcx>) -> String {
        self.just_pred_name_with_args(instance.def_id(), instance.args)
    }

    pub fn mark_pred_as_compiled(&mut self, pred_name: String) {
        self.item_queue.mark_as_done(pred_name);
    }

    pub fn resolve_predicate_param_env(
        &mut self,
        param_env: ParamEnv<'tcx>,
        did: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> (String, DefId, GenericArgsRef<'tcx>) {
        let (instance, item) = match resolve_candidate(self.tcx, param_env, did, args) {
            ResolvedImpl::Param => {
                let instance = Instance::new(did, args);
                let item = AutoItem::ParamPred(param_env, instance);
                (instance, item)
            }
            ResolvedImpl::Impl(instance) => {
                let item = AutoItem::MonoPred(param_env, instance);
                (instance, item)
            }
        };
        let name = self.just_pred_name_instance(instance);
        self.item_queue.push(name.clone(), item);
        (name, instance.def_id(), instance.args)
    }

    pub fn try_resolve(
        &mut self,
        param_env: ParamEnv<'tcx>,
        did: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match resolve_candidate(self.tcx, param_env, did, args) {
            ResolvedImpl::Param => None,
            ResolvedImpl::Impl(instance) => Some((instance.def_id(), instance.args)),
        }
    }

    pub(crate) fn resolve_inner_pred(
        &mut self,
        outer: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> String {
        let name = self.tcx().def_path_str_with_args(outer, args) + "$$inner";
        let auto_item = AutoItem::InnerPred(InnerPred::new(name.clone(), outer, args));
        self.item_queue.push(name.clone(), auto_item);
        name
    }

    pub fn register_mono_spec(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) -> String {
        let name = self.tcx().def_path_str_with_args(def_id, args);
        self.item_queue.push(
            name.clone(),
            MonoSpec::new(name.clone(), def_id, args).into(),
        );
        name
    }

    pub fn add_items_to_prog(&mut self, prog: &mut Prog) {
        while let Some((_, item)) = self.item_queue.pop() {
            item.add_to_prog(prog, self)
        }
    }

    pub fn flush_remaining_defs_to_prog(&mut self, prog: &mut Prog) {
        self.add_items_to_prog(prog);
    }

    pub fn predicate(&self, def_id: DefId) -> &gilsonite::Predicate<'tcx> {
        if !def_id.is_local() {
            let ret = self.metadata.predicate(def_id).unwrap();
            log::trace!("Found predicate in metadata: {:?}", ret);
            return self.metadata.predicate(def_id).unwrap();
        }

        self.assertions.insert(def_id, |_| {
            let (thir, e) = get_thir!(self, def_id);
            let g = GilsoniteBuilder::new(thir.clone(), self.tcx());
            Box::new(g.build_predicate(e))
        })
    }

    // Gets the DefId holding the gilsonite specification for `def_id`
    //
    // TODO: Integrate this cacluation directly into gilsonite spec so it accepts
    // id of the specified item rather than this intermediate fake id
    pub(crate) fn specification_id(&mut self, def_id: DefId) -> Option<DefId> {
        self.spec_map.get(&def_id).cloned()
    }

    pub fn gilsonite_spec(&self, def_id: DefId) -> Option<&'_ SpecTerm<'tcx>> {
        if !def_id.is_local() {
            return self.metadata.specification(def_id);
        }

        self.spec_terms
            .insert(def_id, |_| {
                let (thir, e) = get_thir!(self, def_id);
                let g = GilsoniteBuilder::new(thir.clone(), self.tcx());
                let spec = g.build_spec(e);
                Box::new(Some(spec))
            })
            .as_ref()
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
        self.adt_queue.push(def, ());
    }

    // This takes a self, because it's the last thing that should be done with the global env.
    // After that, encoding any type might lead to compilation forgetting to include it in the
    // initialization data.
    pub(crate) fn serialized_adt_declarations(&mut self) -> serde_json::Value {
        use serde_json::{Map, Value};
        let mut obj: Map<String, Value> = Map::new();
        while let Some((adt, ())) = self.adt_queue.pop() {
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

    pub(crate) fn body_with_facts(&self, def_id: LocalDefId) -> &BodyWithBorrowckFacts<'tcx> {
        self.bodies.insert(def_id, |_| {
            let body = callbacks::get_body(self.tcx, def_id)
                .unwrap_or_else(|| panic!("did not find body for {def_id:?}"));
            Box::new(body)
        })
    }

    pub(crate) fn metadata(&self) -> crate::metadata::BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(&self.assertions, &self.spec_terms, &self.spec_map)
    }
}

#[derive(Debug, Default, Clone, TyDecodable, TyEncodable)]
pub struct GillianItems {
    pub symbol_to_id: HashMap<Symbol, DefId>,
}

pub(crate) fn local_gillian_items(tcx: TyCtxt) -> GillianItems {
    let mut items: GillianItems = Default::default();

    for owner in tcx.hir().body_owners() {
        if let Some(attr) = get_attr(
            tcx.get_attrs_unchecked(owner.to_def_id()),
            &["gillian", "item"],
        ) {
            let def_id = owner.to_def_id();

            items.symbol_to_id.insert(attr.value_str().unwrap(), def_id);
        }
    }

    items
}

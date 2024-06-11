use std::{
    collections::HashMap,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

use crate::logic::gilsonite::{Predicate, SpecTerm};
use creusot_metadata::{decode_metadata, encode_metadata};
use indexmap::IndexMap;
use once_map::OnceMap;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::OutputType;

pub struct Metadata<'tcx> {
    assertions: IndexMap<DefId, Predicate<'tcx>>,
    contracts: IndexMap<DefId, SpecTerm<'tcx>>,
}

impl<'tcx> Metadata<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            assertions: Default::default(),
            contracts: Default::default(),
        }
    }

    pub(crate) fn predicate(&self, def_id: DefId) -> Option<&Predicate<'tcx>> {
        assert!(!def_id.is_local());
        self.assertions.get(&def_id)
    }

    pub(crate) fn specificaiton(&self, def_id: DefId) -> Option<&SpecTerm<'tcx>> {
        assert!(!def_id.is_local());
        self.contracts.get(&def_id)
    }

    pub fn load(tcx: TyCtxt<'tcx>, overrides: &HashMap<String, String>) -> Self {
        let mut meta = Metadata::new();

        for cnum in external_crates(tcx) {
            let base_path = gillian_metadata_base_path(tcx, overrides, cnum);
            let binary_path = gillian_metadata_binary_path(base_path.clone());

            if let Some(metadata) = load_binary_metadata(tcx, cnum, &binary_path) {
                for (def_id, summary) in metadata.assertions.into_iter() {
                    meta.assertions.insert(def_id, summary);
                }
            } else if tcx.crate_name(cnum).as_str() == "gilogic" {
                tcx.dcx().fatal("Could not load metadata for gilogic")
            }
        }

        meta
    }
}

// We use this type to perform (de)serialization of metadata because for annoying
// `extern crate` related reasons we cannot use the instance of `TyEncodable` / `TyDecodable`
// for `IndexMap`. Instead, we flatten it to a association list and then convert that into
// a proper index map after parsing.
#[derive(TyDecodable, TyEncodable)]
pub(crate) struct BinaryMetadata<'tcx> {
    assertions: Vec<(DefId, Predicate<'tcx>)>,
    contracts: Vec<(DefId, SpecTerm<'tcx>)>,
}

impl<'tcx> BinaryMetadata<'tcx> {
    pub(crate) fn from_parts(
        assertions: &OnceMap<DefId, Box<Predicate<'tcx>>>,
        contracts: &OnceMap<DefId, Box<SpecTerm<'tcx>>>,
    ) -> Self {
        let assertions = assertions
            .read_only_view()
            .iter()
            .filter(|(def_id, _)| def_id.is_local())
            .map(|(id, t)| (*id, (&**t).clone()))
            .collect();

        let contracts = contracts
            .read_only_view()
            .iter()
            .filter(|(def_id, _)| def_id.is_local())
            .map(|(id, t)| (*id, (&**t).clone()))
            .collect();

        BinaryMetadata {
            assertions,
            contracts,
        }
    }
}

fn export_file(tcx: TyCtxt, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = tcx.output_filenames(());
        let out = outputs.path(OutputType::Metadata);
        let path = out.as_path().to_owned();
        let path = path.with_extension("gmeta");
        path
    })
}

pub(crate) fn dump_exports<'tcx>(
    tcx: TyCtxt<'tcx>,
    metadata: BinaryMetadata<'tcx>,
    out: &Option<String>,
) {
    let out_filename = export_file(tcx, out);
    let dir = out_filename.parent().unwrap();
    std::fs::create_dir_all(dir).unwrap();
    dump_binary_metadata(tcx, &out_filename, metadata).unwrap_or_else(|err| {
        panic!(
            "could not save metadata path=`{:?}` error={}",
            out_filename, err.1
        )
    });
}

fn dump_binary_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    dep_info: BinaryMetadata<'tcx>,
) -> Result<(), (PathBuf, std::io::Error)> {
    encode_metadata(tcx, path, dep_info)
}

fn load_binary_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    cnum: CrateNum,
    path: &Path,
) -> Option<BinaryMetadata<'tcx>> {
    let mut blob = Vec::new();
    match File::open(path).and_then(|mut file| file.read_to_end(&mut blob)) {
        Ok(_) => (),
        Err(e) => {
            log::warn!(
                "could not read metadata for crate `{:?}`: {:?}",
                tcx.crate_name(cnum),
                e
            );
            return None;
        }
    }

    Some(decode_metadata(tcx, &blob))
}

fn gillian_metadata_base_path(
    tcx: TyCtxt,
    overrides: &HashMap<String, String>,
    cnum: CrateNum,
) -> PathBuf {
    if let Some(path) = overrides.get(&tcx.crate_name(cnum).to_string()) {
        // debug!("loading crate {:?} from override path", cnum);
        path.into()
    } else {
        let cs = tcx.used_crate_source(cnum);
        let x = cs.paths().next().unwrap().clone();
        x
    }
}

fn gillian_metadata_binary_path(mut path: PathBuf) -> PathBuf {
    path.set_extension("gmeta");
    path
}

fn external_crates(tcx: TyCtxt<'_>) -> Vec<CrateNum> {
    let mut deps = Vec::new();
    for cr in tcx.crates(()) {
        if let Some(extern_crate) = tcx.extern_crate(cr.as_def_id()) {
            if extern_crate.is_direct() {
                deps.push(*cr);
            }
        }
    }
    deps
}

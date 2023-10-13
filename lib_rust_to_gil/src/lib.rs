#![deny(rustc::internal)]
#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(cell_leak)]
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_fs_util;
extern crate rustc_hir;
extern crate rustc_incremental;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod prelude {
    pub(crate) use crate::codegen::context::GilCtxt;
    pub(crate) use crate::codegen::typ_encoding::{EncodedType, TypeEncoder};
    pub(crate) use crate::codegen::{names, runtime};
    pub(crate) use crate::global_env::*;
    pub(crate) use crate::utils::tcx_utils::*;
    pub(crate) use gillian::gil::*;
    // pub(crate) use rustc_data_structures::fx::FxHashMap;
    pub(crate) use crate::utils::ty as ty_utils;
    pub(crate) use rustc_middle::mir::{self, *};
    pub(crate) use rustc_middle::ty::{Instance, Ty, TyCtxt, TyKind, ValTree};
    pub(crate) use rustc_span::{def_id::DefId, Symbol};
}

mod codegen;
mod global_env;
mod logic;
mod prog_context;
mod temp_gen;
pub mod utils;

pub mod callbacks;
pub mod config;

#![deny(rustc::internal)]
#![feature(rustc_private)]
#![feature(try_trait_v2)]
#![feature(box_patterns)]
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_fs_util;
extern crate rustc_hir;
extern crate rustc_incremental;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

mod prelude {
    pub(crate) use crate::codegen::context::GilCtxt;
    pub(crate) use crate::codegen::place::PlaceAccess;
    pub(crate) use crate::codegen::{names, runtime};
    pub(crate) use crate::utils::macros::*;
    pub(crate) use gillian::gil::*;
    pub(crate) use rustc_data_structures::fx::FxHashMap;
    pub(crate) use rustc_middle::mir::{self, *};
    pub(crate) use rustc_middle::ty::{Instance, Ty, TyCtxt, TyKind, TyS};
}

mod backend;
mod codegen;
mod emit;
mod utils;

use rustc_codegen_ssa::traits::CodegenBackend;

#[no_mangle]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    backend::GilCodegenBackend::new()
}

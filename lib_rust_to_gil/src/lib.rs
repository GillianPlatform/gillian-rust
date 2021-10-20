#![allow(non_camel_case_types)]
#![allow(dead_code)]
#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;

pub mod ast_print;
pub mod body_ctx;
pub mod compile;
pub mod config;
pub mod gil;
pub mod names;

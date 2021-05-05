#![allow(non_camel_case_types)]
#![allow(dead_code)]
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;

pub mod compile;
pub mod config;
pub mod gil;

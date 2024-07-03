#![allow(internal_features)]
// #![feature(register_tool)]
#![feature(ptr_internals)]
// #![feature(rustc_attrs, stmt_expr_attributes, proc_macro_hygiene)]
#![register_tool(gillian)]

use creusillian::*;
use gilogic::{RustAssertion, Seq, macros::*, prophecies::*};
use std::marker::PhantomData;

fn main() {
    
}

#[creusillian::requires((*x)@.len() == 0)]
fn index_bad(x: &mut vec::Vec<i32>) {
    x.index_mut(0);
}


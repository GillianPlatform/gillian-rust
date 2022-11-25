#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![register_tool(gillian)]

mod tys;

use std::marker::PhantomData;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::{assertion, predicate};
}

pub struct Seq<T>(PhantomData<T>);

#[path = "stubs.rs"]
pub mod __stubs;

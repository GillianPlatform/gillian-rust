#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![register_tool(gillian)]

mod tys;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::*;
}

mod seq;
pub use seq::Seq;

mod ownable;
pub use ownable::Ownable;
mod repr;
pub use repr::ShallowRepresentation;

#[path = "stubs.rs"]
pub mod __stubs;

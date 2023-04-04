#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![register_tool(gillian)]

mod tys;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::*;

    #[macro_export]
    macro_rules! open_borrow {
        ($p:ident ($($args:tt),*)) => {
            ::std::concat_idents!($p,_____open) ($($args),*)
        };
    }

    #[macro_export]
    macro_rules! close_borrow {
        ($p:ident ($($args:tt),*)) => {
            ::std::concat_idents!($p,_____close) ($($args),*)
        };
    }
}

mod seq;
pub use seq::Seq;

mod ownable;
pub use ownable::{Ownable, Prophecised};
mod prophecies;
pub use prophecies::*;

#[path = "stubs.rs"]
pub mod __stubs;

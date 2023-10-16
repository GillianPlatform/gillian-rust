#![allow(internal_features)]
#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![register_tool(gillian)]

mod tys;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::{
        assertion, assertion_test, borrow, close_borrow, ensures, extract_lemma, lemma,
        open_borrow, predicate, requires, show_safety,
    };
    pub mod prophecies {
        pub use gilogic_proc::with_freeze_lemma_for_mutref_pcy as with_freeze_lemma_for_mutref;
    }
    pub mod no_prophecies {
        pub use gilogic_proc::with_freeze_lemma_for_mutref_no_pcy as with_freeze_lemma_for_mutref;
    }
}

mod seq;
pub use seq::Seq;

mod ownable;
pub use ownable::Ownable;
pub mod prophecies;

#[path = "stubs.rs"]
pub mod __stubs;

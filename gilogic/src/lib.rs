#![allow(internal_features)]
#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![feature(ptr_internals)]
#![feature(allocator_api)]
#![feature(tuple_trait, unboxed_closures)]
#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![register_tool(gillian)]

mod tys;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::{
        assertion, assertion_test, borrow, close_borrow, extract_lemma, lemma, open_borrow,
        predicate, show_safety, specification,
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
pub mod alloc;
pub mod iterated;
pub mod prophecies;

pub mod symex_ctrl {

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::symex_ctrl::symex_next"]
    #[inline(always)]
    pub fn symex_next() {}
}

#[path = "stubs.rs"]
pub mod __stubs;

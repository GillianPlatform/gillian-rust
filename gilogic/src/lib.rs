#![allow(internal_features)]
#![feature(never_type)]
#![feature(ptr_internals)]
#![feature(allocator_api)]
#![feature(tuple_trait, unboxed_closures)]
#![cfg_attr(not(gillian), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![cfg_attr(not(gillian), feature(rustc_attrs))]
#![cfg_attr(not(gillian), feature(register_tool))]
#![cfg_attr(not(gillian), register_tool(gillian))]

mod tys;

pub use tys::RustAssertion;

pub mod macros {
    pub use gilogic_proc::{
        assert_bind, assertion, assertion_test, borrow, close_borrow, extract_lemma, formula,
        lemma, open_borrow, predicate, show_safety, specification, with_freeze_lemma,
    };
    // pub mod prophecies {
    //     pub use gilogic_proc::with_freeze_lemma_for_mutref_pcy as with_freeze_lemma_for_mutref;
    // }
    // pub mod no_prophecies {
    //     pub use gilogic_proc::with_freeze_lemma_for_mutref_no_pcy as with_freeze_lemma_for_mutref;
    // }
}

mod seq;
pub use seq::Seq;

pub mod ownable;
pub use ownable::{FrozenOwn, Ownable};
pub mod alloc;
mod iterated_no_pcy;
mod iterated_pcy;

pub mod iterated {
    pub mod with_prophecies {
        pub use crate::iterated_pcy::*;
    }
    pub mod no_prophecies {
        pub use crate::iterated_no_pcy::*;
    }
}

pub mod lemma;
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

#![feature(rustc_attrs)]
#![feature(never_type)]
#![feature(register_tool)]
#![register_tool(gillian)]

mod tys;

pub use tys::RustAssertion;

pub mod macros {

    #[cfg(feature = "gillian_contracts")]
    pub use gilogic_proc::{assertion, ensures, predicate, requires};

    #[cfg(not(feature = "gillian_contracts"))]
    pub use gilogic_proc_dummy::{assertion, ensures, predicate, requires};

    #[cfg(not(any(feature = "gillian_contracts", feature = "creusot_contracts")))]
    pub mod creusillian {
        pub use gilogic_proc_dummy::creusillian_ensures as ensures;
        pub use gilogic_proc_dummy::creusillian_requires as requires;
        pub use gilogic_proc_dummy::representation;
    }
}

mod seq;
pub use seq::Seq;

#[path = "stubs.rs"]
pub mod __stubs;

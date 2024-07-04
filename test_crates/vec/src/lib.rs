#![allow(internal_features)]
#![feature(ptr_internals)]
#![cfg_attr(
    gillian,
    feature(register_tool, rustc_attrs, stmt_expr_attributes, proc_macro_hygiene)
)]
#![cfg_attr(gillian, register_tool(gillian))]

use creusillian::*;
use gilogic::{macros::*, prophecies::*, RustAssertion, Seq};
use std::marker::PhantomData;

pub struct Vec<T> {
    _data: PhantomData<T>,
}

#[cfg(creusot)]
mod creusot_defs {
	// In a module to deal with imports
	use creusot_contracts::*;
    impl<T> ShallowModel for super::Vec<T> {
        type ShallowModelTy = Seq<T>;

        #[trusted]
        #[logic]
        #[open]
        fn shallow_model(self) -> Self::ShallowModelTy {
            pearlite! { absurd }
        }
    }
}

impl<T: Ownable> Ownable for Vec<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, repr: Seq<T::RepresentationTy>) -> RustAssertion {
        assertion!(emp)
    }

    #[cfg(not(gillian))]
    fn own(self, repr: Seq<T::RepresentationTy>) -> RustAssertion {
        unreachable!("")
    }
}

impl<T: Ownable> Vec<T> {
    #[creusillian::requires(ix@ < (*self)@.len())]
    // #[creusillian::ensures(*ret == (*self)@.at(ix@))]
    // #[creusillian::ensures(^ret == (^self)@.at(ix@))]
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    // #[creusillian::ensures(ret@ == (self)@.len())]
    #[creusot_contracts::trusted]
    pub fn len(&self) -> usize {
        0
    }
}

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
use creusot_contracts::logic::IndexLogic;
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
        #[ensures(result.len() <= usize::MAX@)]
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
    #[creusillian::ensures(*result == (*self)@[ix@])]
    #[creusillian::ensures(^result == (^self)@[ix@])]
    #[creusillian::ensures((*self)@.len() == (^self)@.len())]
    #[creusillian::ensures(forall<i : _> 0 <= i && i != ix@ && i < (*self)@.len() ==> (*self)@[i] == (^self)@[i])]
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::ensures((^self)@ == (*self)@.push(e))]
    pub fn push(&mut self, e: T) {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[requires(i@ < self@.len())]
    #[requires(j@ < self@.len())]
    #[ensures((^self)@.exchange(self@, i@, j@))]
    pub fn swap(&mut self, i: usize, j: usize) {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusillian::ensures(result@ == (*self)@.len())]
    #[creusot_contracts::trusted]
    pub fn len(&self) -> usize {
        0
    }
}


#[creusot_contracts::trusted]
pub struct LinkedList<T> {
    _data: PhantomData<T>,
}

impl<T> LinkedList<T> {
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::requires(true)]
    // #[creusillian::ensures(match result {
    //     None => ^self == *self,
    //     Some(a) => (^self)@.push(a) == (*self)@
    // })]
    // #[creusillian::ensures((*self)@ == (^self).push(e))]
    pub fn pop_front(&mut self) -> Option<T> {
        todo!()
    }
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::requires(true)]
    // #[creusillian::ensures((^self)@ == (*self)@.push(e))]
    pub fn push_front(&mut self, e: T) {
        todo!()
    }
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    // #[creusillian::ensures(result@.len() == 0)]
    #[creusillian::requires(true)]
    pub fn new() -> Self {
        todo!()
    }
}


#[cfg(creusot)]
mod creusot_defs2 {
    // In a module to deal with imports
    use creusot_contracts::*;
    impl<T> ShallowModel for super::LinkedList<T> {
        type ShallowModelTy = Seq<T>;

        #[trusted]
        #[logic]
        #[open(self)]
        fn shallow_model(self) -> Self::ShallowModelTy {
            pearlite! { absurd }
        }
    }
}

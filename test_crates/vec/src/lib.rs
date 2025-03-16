#![allow(internal_features)]
#![feature(ptr_internals)]

use creusillian::*;
use creusot_contracts::logic::ops::IndexLogic;
use gilogic::{macros::*, prophecies::*, RustAssertion, Seq};
use std::marker::PhantomData;

#[creusot_contracts::trusted]
pub struct Vec<T> {
    _data: PhantomData<T>,
}

#[cfg(creusot)]
mod creusot_defs {
    // In a module to deal with imports
    use creusot_contracts::*;
    impl<T> View for super::Vec<T> {
        type ViewTy = Seq<T>;

        #[trusted]
        #[logic]
        #[open]
        #[ensures(result.len() <= usize::MAX@)]
        fn view(self) -> Self::ViewTy {
            pearlite! { dead }
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
    #[creusot_contracts::trusted]
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
    #[creusillian::ensures((^self)@ == (*self)@.push_back(e))]
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

    #[creusot_contracts::trusted]
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusillian::ensures(match result {
    None => (((*self)@.len() <= ix@) && (*self == ^self)),
    Some(r) =>
        ((*self)@[ix@] == (*r)) &&
        ((^self)@[ix@] == (^r)) &&
        ((^self)@ == (*self)@.subsequence(0, ix@).push_back((^r)).concat((*self)@.subsequence(ix@ + 1, (*self)@.len() - ix@ - 1)))
    })]
    pub fn get_mut(&mut self, ix: usize) -> Option<&mut T> {
        todo!()
    }

    #[creusot_contracts::trusted]
    #[creusillian::ensures(result@ == creusot_contracts::Seq::EMPTY)]
    pub const fn new() -> Self {
        todo!()
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
    //     None => ^self == *self && self@.len() == 0,
    //     Some(a) => creusot_contracts::Seq::singleton(a).concat((^self)@) == (*self)@
    //     // Some(a) => (^self)@ == (*self)@.tail() && self@[0] == a
    // })]
    #[creusillian::ensures(
        forall<x : _> result == Some(x) ==> ((^self)@).push_front(x) == (*self)@)]
    #[creusillian::ensures(result == None ==> ^self == *self && self@.len() == 0)]
    // #[creusillian::ensures((*self)@ == (^self)@.push_back(e))]
    pub fn pop_front(&mut self) -> Option<T> {
        todo!()
    }
    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::requires(true)]
    #[creusillian::ensures(creusot_contracts::Seq::singleton(e).concat((*self)@) == (^self)@)]
    pub fn push_front(&mut self, e: T) {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::requires(true)]
    #[creusillian::ensures((*self)@.push_back(e) == (^self)@)]
    pub fn push_back(&mut self, e: T) {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::ensures(result@.len() == 0)]
    #[creusillian::requires(true)]
    pub fn new() -> Self {
        todo!()
    }

    #[cfg_attr(gillian, gillian::trusted)]
    #[creusot_contracts::trusted]
    #[creusillian::ensures(result == ((*self)@.len() == 0))]
    #[creusillian::ensures((*self)@ == (^self)@)]
    pub fn is_empty(&mut self) -> bool {
        todo!()
    }
}

#[cfg(creusot)]
mod creusot_defs2 {
    // In a module to deal with imports
    use creusot_contracts::*;
    impl<T> View for super::LinkedList<T> {
        type ViewTy = Seq<T>;

        #[trusted]
        #[logic]
        #[open(self)]
        fn view(self) -> Self::ViewTy {
            pearlite! { dead }
        }
    }
}

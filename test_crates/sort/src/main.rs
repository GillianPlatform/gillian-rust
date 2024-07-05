#![allow(internal_features)]
// #![feature(register_tool)]
#![feature(ptr_internals)]
// #![feature(rustc_attrs, stmt_expr_attributes, proc_macro_hygiene)]
#![register_tool(gillian)]

use creusillian::*;
use gilogic::{RustAssertion, Seq, macros::*, prophecies::*};
use creusot_contracts::{Snapshot, snapshot, logic::IndexLogic};

#[creusillian::requires((*x)@.len() == 0)]
fn index_bad(x: &mut vec::Vec<i32>) {
    x.index_mut(0);
}

fn main() { }

#[cfg_attr(gillian, trusted)]
#[creusillian::ensures((^str)@.len() >= len@ && (^str)@.len() >= str@.len())]
#[creusillian::ensures((^str)@.len() == len@ || (^str)@.len() == str@.len())]
#[creusillian::ensures(forall<i: _> 0 <= i && i < ((^str)@.len() - str@.len()) ==> (^str)[i] == pad)]
#[creusillian::ensures(forall<i: _> 0 <= i && i < str@.len() ==> (^str)[i + ((^str)@.len() - str@.len())] == str[i])]
fn left_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = creusot_contracts::snapshot! { str };
    let mut c: Snapshot<_> = creusot_contracts::snapshot! { 0 };

    #[creusot_contracts::invariant(^str == ^*old_str)]
    #[creusot_contracts::invariant(old_str@.len() <= str@.len())]
    #[creusot_contracts::invariant(old_str@.len() < len@ ==> str@.len() <= len@)]
    #[creusot_contracts::invariant(str@.len() > len@ ==> str@.len() == old_str@.len())]
    #[creusot_contracts::invariant(*c == str@.len() - old_str@.len())]
    #[creusot_contracts::invariant(forall<i: _> *c <= i && i < str@.len() ==> str[i] == old_str[i - *c])]
    #[creusot_contracts::invariant(forall<i: _> 0 <= i && i < *c ==> str[i] == pad)]
    while str.len() < len {
        str.insert(0, pad);
        c = snapshot! { 1 + *c };
    }
}
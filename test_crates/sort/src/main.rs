#![allow(internal_features)]
// #![feature(register_tool)]
#![feature(ptr_internals)]
// #![feature(rustc_attrs, stmt_expr_attributes, proc_macro_hygiene)]
#![register_tool(gillian)]

use creusillian::*;
use gilogic::{RustAssertion, Seq, macros::*, prophecies::*};
use creusot_contracts::{Snapshot, snapshot, logic::IndexLogic};

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


#[cfg_attr(gillian, trusted)]
#[ensures(forall<i : _, j : _> 0 <= i && i < j && j < v@.len() ==> (^v)@[i] <= (^v)@[j])]
#[ensures((^v)@.permutation_of(v@))]
pub fn gnome_sort(v: &mut Vec<i32>)
{
    let old_v = snapshot! { v };
    let mut i = 0;
    #[creusot_contracts::invariant(^*old_v == ^v)]
    #[creusot_contracts::invariant(forall<k : _, j : _> 0 <= k && k < j && j < i@ ==> v@[k] <= v@[j])]
    #[creusot_contracts::invariant(v@.permutation_of(old_v@))]
    while i < v.len() {
        if i == 0 || v[i - 1] <= v[i] {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}


#[cfg_attr(gillian, trusted)]
#[ensures(forall<i : _, j : _> 0 <= i && i < j && j < v@.len() ==> (^v)@[i] <= (^v)@[j])]
#[ensures((^v)@.permutation_of(v@))]
pub fn selection_sort(v: &mut Vec<i32>)
{
    let old_v = snapshot! { v };
    #[creusot_contracts::invariant(v@.permutation_of(old_v@))]
    #[creusot_contracts::invariant(forall<i : _, j : _> 0 <= i && i < j && j < produced.len() ==> v@[i] <= v@[j])]
    #[creusot_contracts::invariant( forall<k1 : _, k2: _> 0 <= k1 && k1 < produced.len() && produced.len() <= k2 && k2 < v@.len() ==> v@[k1] <= v@[k2])]
    for i in 0..v.len() {
        let mut min = i;

        #[creusot_contracts::invariant(forall<k: _> i@ <= k && k < produced.len() + i@ + 1 ==> v@[min@] <= v@[k])]
        #[creusot_contracts::invariant(i@ <= min@ && min@ < produced.len() + i@ + 1)]
        for j in (i + 1)..v.len() {
            if v[j] < v[min] {
                min = j;
            }
        }
        v.swap(i, min);
        creusot_contracts::proof_assert! { let i = produced.len();
            forall<k1 : _, k2: _> 0 <= k1 && k1 < i && i <= k2 && k2 < v@.len() ==> v@[k1] <= v@[k2] };
    }
}

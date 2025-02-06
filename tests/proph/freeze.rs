//@ check-pass
extern crate creusillian;
extern crate gilogic;

use gilogic::{
    macros::*,
    prophecies::{Ownable, Prophecised, Prophecy},
};

struct A {
    x: u64,
    y: u64,
}

#[with_freeze_lemma(
    lemma_name = freeze_x,
    predicate_name = a_ref_mut_x,
    frozen_variables = [x]
)]
impl Ownable for A {
    type RepresentationTy = u64;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|x: u64, y| (self == A { x, y }) * (model == x) * (y == x + 1))
    }
}

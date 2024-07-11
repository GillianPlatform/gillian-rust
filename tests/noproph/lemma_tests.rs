//@check-pass
extern crate gilogic;

use gilogic::{
    macros::{no_prophecies::with_freeze_lemma_for_mutref, *},
    assert_bind,
    Ownable,
};

#[lemma]
#[specification(
    requires { (a > b) }
    ensures { emp }
)]
fn test_lemma((a, b) : (i32, i32)) {
    if true {

    } else {

    }
}

#[lemma]
#[specification(
    requires { (a > b) }
    ensures { emp }
)]
fn test_lemma2((a, b) : (i32, i32)) {
    // assert_bind!(x, y | (x == a) * (y == b));

    // if x > 0 {

    // } else {

    // };
}
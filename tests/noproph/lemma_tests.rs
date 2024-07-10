//@check-pass
extern crate gilogic;

use gilogic::{
    macros::{no_prophecies::with_freeze_lemma_for_mutref, *},
    Ownable,
};

#[lemma]
#[specification(
    requires { (a > b) }
    ensures { emp }
)]
fn test_lemma((a, b) : (i32, i32)) {

}
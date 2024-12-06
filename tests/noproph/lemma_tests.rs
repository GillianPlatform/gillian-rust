//@check-pass
extern crate gilogic;

use gilogic::{macros::*, Ownable};

#[lemma]
#[specification(
    requires { (a > b) }
    ensures { emp }
)]
fn test_lemma((a, b): (i32, i32)) {
    if true {
    } else {
    }
}

#[lemma]
#[specification(
    requires { (a > b) }
    ensures { emp }
)]
fn test_lemma2((a, b): (i32, i32)) {
    assert_bind!(x, y | (x == a) * (y == b));
    assert_bind!((y < x));
    if x > 0 {
    } else {
    };
}

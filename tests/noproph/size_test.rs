//@check-pass
extern crate gilogic;

use gilogic::{macros::*, Ownable};

struct Test {
    x: u32,
    y: u16,
}

#[show_safety]
fn test() {
    assert!(std::mem::size_of::<Test>() >= 6);
}

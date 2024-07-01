//@check-pass
extern crate gilogic;

use gilogic::{macros::show_safety, Ownable};

#[show_safety]
fn test<T: Ownable>(x: Box<T>) -> T {
    return *x;
}

#[show_safety]
fn test2() -> i32 {
    test(Box::new(12))
}

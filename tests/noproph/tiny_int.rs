//@check-pass
extern crate gilogic;

use gilogic::{macros::*, Ownable};

struct MyInt(u32);

impl Ownable for MyInt {
    #[predicate]
    fn own(self) {
        assertion!((0 <= self.0) * (self.0 <= 10))
    }
}

impl MyInt {
    #[show_safety]
    fn new(x: u32) -> Option<Self> {
        if x > 10 {
            None
        } else {
            Some(MyInt(x))
        }
    }
}

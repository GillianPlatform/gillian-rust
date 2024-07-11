//@check-pass
extern crate creusillian;
extern crate gilogic;

use gilogic::macros::{assertion, predicate};
use gilogic::mutref_auto_resolve;
use gilogic::prophecies::{Ownable, Prophecised};

struct EvenInt {
    num: i32,
}

impl Ownable for EvenInt {
    type RepresentationTy = i32;

    #[predicate]
    fn own(self, model: i32) {
        assertion!((self == EvenInt { num: model }) * (model % 2 == 0));
    }
}

impl EvenInt {
    #[creusillian::ensures(true)]
    pub fn new_2(x: i32) -> Self {
        if x % 2 == 0 {
            Self { num: x }
        } else {
            if x < 1000 {
                Self { num: x + 1 }
            } else {
                Self { num: x - 1 }
            }
        }
    }

    pub unsafe fn new(x: i32) -> Self {
        Self { num: x }
    }

    #[creusillian::ensures(true)]
    pub fn new_3(x: i32) -> Option<Self> {
        if x % 2 == 0 {
            let y = unsafe { Self::new(x) };
            Some(y)
        } else {
            None
        }
    }

    unsafe fn add(&mut self) {
        self.num += 1;
    }

    #[creusillian::ensures(true)]
    pub fn test(&mut self) {
        if self.num % 2 != 0 {
            panic!()
        }
    }

    #[creusillian::requires((*self@) <= i32::MAX@ - 2)]
    #[creusillian::ensures((^self@) == (*self@) + 2)]
    pub fn add_two(&mut self) {
        self.num;

        unsafe {
            self.add();
            self.add();
        }
        mutref_auto_resolve!(self);
    }
}

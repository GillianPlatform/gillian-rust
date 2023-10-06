extern crate gilogic;

use gilogic::{macros::*, Ownable};

pub enum Option<T> {
    None,
    Some(T),
}

impl<T: Ownable> Ownable for Option<T> {
    #[predicate]
    fn own(self) {
        assertion!((self == Self::None));
        assertion!(|x| (self == Self::Some(x)) * x.own())
    }
}

impl<T: Ownable> Option<T> {
    #[show_safety]
    pub fn new(x: T) -> Self {
        Self::Some(x)
    }

    #[show_safety]
    pub fn put(&mut self, x: T) {
        *self = Self::Some(x)
    }
}

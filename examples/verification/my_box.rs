extern crate gilogic;

struct MyBox<T> {
    ptr: *mut T,
}

use gilogic::{
    macros::{assertion, predicate, show_safety},
    Ownable,
};

impl<T: Ownable> Ownable for MyBox<T> {
    #[predicate]
    fn own(self) {
        assertion!(|ptr, v| (self == MyBox { ptr }) * (ptr -> v) * v.own())
    }
}

impl<T: Ownable> MyBox<T> {
    #[show_safety]
    fn write(self, v: T) -> Self {
        unsafe { *self.ptr = v };
        self
    }

    #[show_safety]
    fn update(&mut self, v: T) {
        unsafe { *self.ptr = v };
    }
}

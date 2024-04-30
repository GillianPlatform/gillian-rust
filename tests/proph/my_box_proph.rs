//@check-pass
extern crate gilogic;

struct MyBox<T> {
    ptr: *mut T,
}

use gilogic::{
    macros::{assertion, predicate, specification},
    prophecies::Ownable,
};

impl<T: Ownable> Ownable for MyBox<T> {
    type RepresentationTy = T::RepresentationTy;
    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|ptr, v| (self == MyBox { ptr }) * (ptr -> v) * v.own(model))
    }
}

impl<T: Ownable> MyBox<T> {

    #[specification(
        forall sm, vm .
            requires { self.own(sm) * v.own(vm) }
        exists rm, foo: T .
            ensures {   ret.own(rm) * $rm == vm$ }
    )]
    // #[requires(|sm: T::RepresentationTy, vm: T::RepresentationTy| self.own(sm) * v.own(vm) )]
    // #[ensures(|rm: T::RepresentationTy, foo: T|  ret.own(rm) * $rm == vm$ )]
    fn write(self, v: T) -> Self {
        unsafe { *self.ptr = v };
        self
    }

    // #[requires(|sm: (T::RepresentationTy, T::RepresentationTy), vm: T::RepresentationTy| self.own(sm) * v.own(vm))]
    // #[ensures(|rm: T::RepresentationTy| $sm.1 == vm$ * $sm.0 == vm$)]
    // fn update(&mut self, v: T) {
    //     unsafe { *self.ptr = v };
    // }
}

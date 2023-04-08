#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    close_borrow,
    macros::{assertion, borrow, ensures, lemma, predicate, requires, show_safety},
    open_borrow, Ownable,
};

#[repr(C)]
struct WP<T> {
    x: *mut N<T>,
    y: *mut N<T>,
}

#[repr(C)]
struct N<T> {
    v: T,
    o: *mut N<T>,
}

#[predicate]
fn wp<T: Ownable>(wp: In<WP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x, v_y|
        (wp == WP { x, y }) *
        (x -> N { v: v_x, o: y }) *
        (y -> N { v: v_y, o: x }) *
        v_x.own() * v_y.own()
    )
}

impl<T: Ownable> Ownable for WP<T> {
    #[predicate]
    fn own(self) {
        assertion!(|x, y| wp(self, x, y))
    }
}

impl<T: Ownable> WP<T> {
    // #[show_safety]
    // fn drop(&mut self) {
    //     unsafe {
    //         Box::from_raw(self.x);
    //         Box::from_raw(self.y);
    //     }
    // }

    #[show_safety]
    fn new(x: T, y: T) -> Self {
        let null: *mut N<T> = std::ptr::null_mut();

        let xbox = Box::new(N { v: x, o: null });
        let ybox = Box::new(N { v: y, o: null });

        let xptr = Box::leak(xbox) as *mut N<T>;
        let yptr = Box::leak(ybox) as *mut N<T>;

        unsafe {
            (*yptr).o = xptr;
            (*xptr).o = yptr;
        }
        WP { x: xptr, y: yptr }
    }
}

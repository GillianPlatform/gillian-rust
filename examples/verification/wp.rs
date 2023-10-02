#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{macros::*, Ownable};

struct WP<T> {
    x: *mut N<T>,
    y: *mut N<T>,
}

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

#[lemma]
#[requires(|x: *mut N<T>, y: *mut N<T>| wp_ref_mut_xy(p, x, y))]
#[ensures(|r: &mut T| (r == &mut (*x).v) * r.own())]
fn split_x<'a, T: Ownable>(p: &'a mut WP<T>);

#[with_freeze_lemma_for_mutref(
    lemma_name = freeze_xy,
    predicate_name = wp_ref_mut_xy,
    frozen_variables = [x, y],
)]
impl<T: Ownable> Ownable for WP<T> {
    #[predicate]
    fn own(self) {
        assertion!(|x: *mut N<T>, y: *mut N<T>| wp(self, x, y))
    }
}

impl<T: Ownable> WP<T> {
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

    #[show_safety]
    fn assign_first(&mut self, x: T) {
        unsafe {
            (*self.x).v = x;
        }
    }

    #[show_safety]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            freeze_xy(self);
            let ret = &mut (*self.x).v;
            split_x(self);
            ret
        }
    }
}

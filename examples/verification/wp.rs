#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    macros::{
        assertion, borrow, close_borrow, ensures, lemma, open_borrow, predicate, requires,
        show_safety,
    },
    Ownable,
};

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

#[borrow]
fn wp_ref_mut_xy<'a, T: Ownable>(p: In<&'a mut WP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x: T, v_y: T|
        (p -> WP { x, y }) *
        wp(WP { x, y }, x, y)
    )
}

// FIXME: pull lemmas shouldn't require lifetime tokens at all.
#[lemma]
#[requires(p.own())]
#[ensures(|x: *mut N<T>, y: *mut N<T>| wp_ref_mut_xy(p, x, y))]
fn wp_ref_mut_pull_xy<'a, T: Ownable>(p: &'a mut WP<T>);

// FIXME: split lemmas shouldn't require lifetime tokens at all
#[lemma]
#[requires(|x: *mut N<T>, y: *mut N<T>| wp_ref_mut_xy(p, x, y))]
#[ensures(|r: &mut T| (r == &mut (*x).v) * r.own())]
fn split_x<'a, T: Ownable>(p: &'a mut WP<T>);

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

    #[show_safety]
    fn assign_first(&mut self, x: T) {
        unsafe {
            open_borrow!(self.own());
            (*self.x).v = x;
            close_borrow!(self.own());
        }
    }

    #[show_safety]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            wp_ref_mut_pull_xy(self);
            open_borrow!(wp_ref_mut_xy(self, self.x, self.y));
            let ret = &mut (*self.x).v;
            close_borrow!(wp_ref_mut_xy(self, self.x, self.y));
            split_x(self);
            ret
        }
    }

    // A good example of a function that shouldn't be verifiable:
    /*
        fn both_mut<'a>(&'a mut self) -> (&'a mut T, &'a mut T) {
        unsafe {
            (&mut (*self.x).v, &mut(*self.x).v) <- mistake, it should be x and y, not twice x.
        }
    } */
}

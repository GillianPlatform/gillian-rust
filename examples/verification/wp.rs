#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    close_borrow,
    macros::{assertion, borrow, ensures, lemma, predicate, requires, show_safety},
    open_borrow, Ownable,
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

// This creates:
// 1) An abstract predicate called `borrowed_wp_xy` which can be opened.
// 2) An abstract predicate called `borrowed_wp_xy$close_token`.
// 3) A lemma `borrowed_wp_xy$access` which exchanges `borrowed_wp_xy` and a token for `'a` for
//      a) the assertion inside `borrowed_wp_xy` and
//      b) a `borrowed_wp_xy$close_token`
// 4) A lemma `borrowed_wp_xy$close` which exchanges the close_token and the assertion against the `borrowed_wp_xy`.
#[borrow]
fn wp_ref_mut_xy<'a, T: Ownable>(p: In<&'a mut WP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x: T, v_y: T|
        (p -> WP { x, y }) *
        wp(WP { x, y }, x, y)
    )
}

#[borrow]
fn wp_ref_mut<'a, T: Ownable>(p: In<&'a mut WP<T>>) {
    assertion!(|w: WP<T>| (p -> w) * w.own())
}

#[borrow]
fn T_ref_mut<'a, T: Ownable>(p: In<&'a T>) {
    assertion!(|v: T| (p -> v) * v.own())
}

#[lemma]
#[requires(|pp| (p == pp) * wp_ref_mut(pp))]
#[ensures(|pp, x: *mut N<T>, y: *mut N<T>| wp_ref_mut_xy(pp, x, y))]
fn wp_ref_mut_pull_xy<'a, T: Ownable>(p: &'a mut WP<T>);

#[lemma]
#[requires(|pp, x, y| (p == pp) * wp_ref_mut_xy(pp, x, y))]
#[ensures(|x: &mut T| T_ref_mut(x))]
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

    #[requires(wp_ref_mut(self))]
    #[ensures(T_ref_mut(ret))]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        let ptr = self as *mut WP<T>;
        unsafe {
            wp_ref_mut_pull_xy(self);
            open_borrow!(wp_ref_mut_xy(self));
            let ret = &mut (*self.x).v;
            close_borrow!(wp_ref_mut_xy(self));

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

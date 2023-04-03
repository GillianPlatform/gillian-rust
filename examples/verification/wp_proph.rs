#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    close_borrow, controller,
    macros::{assertion, borrow, ensures, lemma, predicate, requires},
    observer, open_borrow, Ownable, Prophecised, ShallowRepresentation,
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
fn wp<T: Ownable>(wp: In<WP<T>>, x: *mut N<T>, y: *mut N<T>, model: (T, T)) {
    assertion!(|v_x, v_y|
        (wp == WP { x, y }) *
        (x -> N { v: v_x, o: y }) *
        (y -> N { v: v_y, o: x }) *
        v_x.own() * v_y.own() *
        (model == (v_x, v_y))
    )
}

#[borrow]
fn wp_ref_mut_inner_xy<'a, T: Ownable>(p: In<&'a mut WP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x: T, v_y: T|
        (p -> WP { x, y }) *
        wp(WP { x, y }, x, y, (v_x, v_y)) * controller(p.prophecy(), (v_x, v_y))
    )
}

#[lemma]
#[requires(|model, pcy|  p.shallow_repr((model, pcy)))]
#[ensures(|x, y|
    (pcy == p.prophecy().value()) *
    observer(p.prophecy(), model) *
    wp_ref_mut_inner_xy(p, x, y)
)]
fn wp_ref_mut_pull_xy<'a, T: Ownable>(p: &'a mut WP<T>);

#[lemma]
#[requires(|x: *mut N<T>, y: *mut N<T>, model: T| wp_ref_mut_inner_xy(p, x, y) * observer(p.prophecy().field_0(), model))]
#[ensures(|r: &mut T| (r == &mut (*x).v) * r.own())]
fn split_x<'a, T: Ownable>(p: &'a mut WP<T>);

impl<T: Ownable> ShallowRepresentation for WP<T> {
    type ShallowModelTy = (T, T);

    #[predicate]
    fn shallow_repr(self, model: Self::ShallowModelTy) {
        assertion!(|x, y| wp(self, x, y, model))
    }
}

impl<T: Ownable> WP<T> {
    #[requires(|lx, ly| (x == lx) * (y == ly) * lx.own() * ly.own())]
    #[ensures(ret.shallow_repr((lx, ly)))]
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

    #[requires(|cself: (T, T), pself: (T, T)| self.shallow_repr((cself, pself)))]
    #[ensures(ret.own() * (cself.1 == pself.1))]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            let prophecy = self.prophecy();
            wp_ref_mut_pull_xy(self);
            open_borrow!(wp_ref_mut_inner_xy(self));
            prophecy.field_1().resolve();
            let ret = &mut (*self.x).v;
            close_borrow!(wp_ref_mut_inner_xy(self));
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

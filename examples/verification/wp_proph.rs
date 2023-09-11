#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    macros::{assertion, borrow, close_borrow, ensures, lemma, open_borrow, predicate, requires},
    prophecies::{controller, observation, observer, Ownable, Prophecised, Prophecy},
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
fn wp<T: Ownable>(
    wp: In<WP<T>>,
    x: *mut N<T>,
    y: *mut N<T>,
    model: (T::RepresentationTy, T::RepresentationTy),
) {
    assertion!(|v_x, v_y, v_x_m, v_y_m|
        (wp == WP { x, y }) *
        (x -> N { v: v_x, o: y }) *
        (y -> N { v: v_y, o: x }) *
        v_x.own(v_x_m) * v_y.own(v_y_m) *
        (model == (v_x_m, v_y_m))
    )
}

#[borrow]
fn wp_ref_mut_inner_xy<'a, T: Ownable>(p: In<&'a mut WP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x: T, v_y: T, v_x_m: T::RepresentationTy, v_y_m: T::RepresentationTy|
        (p -> WP { x, y }) *
        wp(WP { x, y }, x, y, (v_x_m, v_y_m)) * controller(p.prophecy(), (v_x_m, v_y_m))
    )
}

#[lemma]
#[requires(|model, pcy|  p.own((model, pcy)))]
#[ensures(|x, y|
    (pcy == p.prophecy().value()) *
    observer(p.prophecy(), model) *
    wp_ref_mut_inner_xy(p, x, y)
)]
fn wp_ref_mut_pull_xy<'a, T: Ownable>(p: &'a mut WP<T>);

#[lemma]
#[requires(|x: *mut N<T>, y: *mut N<T>| wp_ref_mut_inner_xy(p, x, y))]
#[ensures(|r: &mut T, rp: &mut T| (r == &mut (*x).v) * Ownable::ref_mut_inner(r.with_prophecy(k)))]
fn split_x<'a, T: Ownable>(p: &'a mut WP<T>, k: Prophecy<T::RepresentationTy>);

impl<T: Ownable> Ownable for WP<T> {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|x, y| wp(self, x, y, model))
    }
}

impl<T: Ownable> WP<T> {
    #[requires(|lx: T::RepresentationTy, ly: T::RepresentationTy| x.own(lx) * y.own(ly))]
    #[ensures(|ret_v| ret.own(ret_v) * $ret_v == (lx, ly)$)]
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

    // #[requires(|current: (T::RepresentationTy, T::RepresentationTy),
    //             proph: (T::RepresentationTy, T::RepresentationTy),
    //             xm: T::RepresentationTy|
    //     self.own((current, proph)) * x.own(xm)
    // )]
    // #[ensures(
    //     (proph == (xm, current.1))
    // )]
    // fn assign_first(&mut self, x: T) {
    //     unsafe {
    //         // open_borrow!(self.own());
    //         let ret = (*self.x).v = x;
    //         self.prophecy().assign(self.representation());
    //         self.prophecy().resolve();
    //         // close_borrow!(self.own());
    //         ret
    //     }
    // }

    #[requires(|cself: (T::RepresentationTy, T::RepresentationTy), pself: (T::RepresentationTy, T::RepresentationTy)| self.own((cself, pself)))]
    #[ensures(|c, p| ret.own((c, p)) * (cself.1 == pself.1))]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            let prophecy = self.prophecy();
            wp_ref_mut_pull_xy(self);
            let ret = &mut (*self.x).v;
            prophecy.field_1().resolve();
            split_x(self, ret.prophecy());
            ret
        }
    }
}

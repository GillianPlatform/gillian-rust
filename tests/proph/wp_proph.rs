//@check-pass
#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    macros::{
        assertion, extract_lemma, lemma, predicate, prophecies::with_freeze_lemma_for_mutref,
        specification,
    },
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised, Prophecy},
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

#[with_freeze_lemma_for_mutref(
    lemma_name = freeze_xy,
    predicate_name = wp_ref_mut_xy,
    frozen_variables = [x, y],
    inner_predicate_name = wp_ref_mut_inner_xy
)]
impl<T: Ownable> Ownable for WP<T> {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|x: *mut N<T>, y: *mut N<T>| wp(self, x, y, model))
    }
}

// TODO: I need to not create matching plans for lemmas that do not have a proof!
// Because the prophecy variable in the post condition is just generated out of nowhere.
#[extract_lemma(
    forall p, x: *mut N<T>, y: *mut N<T>.
    model m.
    extract model mx: (T::RepresentationTy, T::RepresentationTy).
    from { wp_ref_mut_xy(p, m, x, y) }
    extract { Ownable::own(&mut (*x).v, mx) }
    prophecise { (mx, m.1) }
)]
fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>) -> Prophecy<T::RepresentationTy>;

//
// fn extract_tuple<T>(p : &mut (T, T)) -> &mut T;

impl<T: Ownable> WP<T> {
    #[specification(
        forall lx, ly.
        requires { x.own(lx) * y.own(ly) }
        exists ret_v.
        ensures { ret.own(ret_v) * $ret_v == (lx, ly)$ }
    )]
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

    #[specification(
        forall current, proph, xm.
        requires { self.own((current, proph)) * x.own(xm) }
        ensures { $proph == (xm, current.1)$ }
    )]
    fn assign_first(&mut self, x: T) {
        unsafe {
            (*self.x).v = x;
            mutref_auto_resolve!(self);
        }
    }

    #[specification(forall cself, pself.
        requires { self.own((cself, pself)) }
        exists c, p.
        ensures {  ret.own((c, p)) * $cself.1 == pself.1 && pself.0 == p && cself.0 == c$ }
    )]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            freeze_xy(self);
            let ret = &mut (*self.x).v;
            let proph = extract_x(self);
            ret.with_prophecy(proph)
        }
    }
}

//@check-pass
//?gil:ignore
#![feature(concat_idents)]

extern crate gilogic;

use gilogic::{
    macros::{
        assertion, lemma, predicate, prophecies::with_freeze_lemma_for_mutref, specification,
    },
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised},
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
    
    #[extract_lemma]
    #[specification(
        forall x, y.
    )
    ]

    #[specification(forall cself, pself.
        requires { self.own((cself, pself)) }
        exists c, p. 
        ensures {  ret.own((c, p)) * $cself.1 == pself.1 && cself.0 == c && pself.0 == p$ }
    )]
    fn first_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            freeze_xy(self);
            let ret = &mut (*self.x).v;
            ret
        }
    }
}

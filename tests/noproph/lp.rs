//@check-pass
extern crate gilogic;

use gilogic::{macros::*, Ownable};

struct LP<T> {
    x: *mut N<T>,
    y: *mut N<T>,
}

struct N<T> {
    v: T,
    o: *mut N<T>,
}

#[predicate]
fn lp<T: Ownable>(lp: In<LP<T>>, x: *mut N<T>, y: *mut N<T>) {
    assertion!(|v_x, v_y|
        (lp == LP { x, y }) *
        (x -> N { v: v_x, o: y }) *
        (y -> N { v: v_y, o: x }) *
        v_x.own() * v_y.own()
    )
}

#[extract_lemma(
    forall x, y.
    from { lp_ref_mut_xy(p, (x, y)) }
    extract { <&mut T as Ownable>::own(&mut (*x).v) }
)]
fn extract_x<'a, T: Ownable>(p: &'a mut LP<T>);

#[extract_lemma(
    forall x, y.
    from { lp_ref_mut_xy(p, (x, y)) }
    extract { <&mut T as Ownable>::own(&mut (*y).v) }
)]
fn extract_y<'a, T: Ownable>(p: &'a mut LP<T>);

#[with_freeze_lemma(
    lemma_name = freeze_xy,
    predicate_name = lp_ref_mut_xy,
    frozen_variables = [x, y],
)]
impl<T: Ownable> Ownable for LP<T> {
    #[predicate]
    fn own(self) {
        assertion!(|x: *mut N<T>, y: *mut N<T>| lp(self, x, y))
    }
}

impl<T: Ownable> LP<T> {
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
        LP { x: xptr, y: yptr }
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
            extract_x(self);
            ret
        }
    }

    #[show_safety]
    fn second_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            freeze_xy(self);
            let ret = &mut (*self.y).v;
            extract_y(self);
            ret
        }
    }
}

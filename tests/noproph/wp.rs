//@check-pass
extern crate gilogic;

use gilogic::{
    macros::{with_freeze_lemma, *},
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

#[extract_lemma(
    forall x, y.
    from { wp_ref_mut_xy(p, x, y) }
    extract { <&mut T as Ownable>::own(&mut (*x).v) }
)]
fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>);

#[extract_lemma(
    forall x, y.
    from { wp_ref_mut_xy(p, x, y) }
    extract { <&mut T as Ownable>::own(&mut (*y).v) }
)]
fn extract_y<'a, T: Ownable>(p: &'a mut WP<T>);

#[with_freeze_lemma(
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

//@check-pass
extern crate gilogic;

use gilogic::{
    macros::{no_prophecies::with_freeze_lemma_for_mutref, *},
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

// #[extract_lemma(
//     forall x, y.
//     from { wp_ref_mut_xy(p, x, y) }
//     extract { <&mut T as Ownable>::own(&mut (*x).v) }
// )]
// fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>);


#[cfg(gillian)]
#[rustc_diagnostic_item =
"extract_x_extract_lemma_182a34a1_599c_49be_91bf_0490844500cf"]
#[gillian::decl::extract_lemma]
fn extract_x_extract_lemma_182a34a1_599c_49be_91bf_0490844500cf<'a,
    T: Ownable>(p: &'a mut WP<T>) -> gilogic::RustAssertion {
    unsafe {
        gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |x, y|
                {
                    gilogic::__stubs::extract_lemma::<()>(gilogic::__stubs::equal(true,
                            true), wp_ref_mut_xy(p, x, y),
                        <&mut T as Ownable>::own(&mut (*x).v), ())
                })
    }
}
#[cfg(gillian)]
#[rustc_diagnostic_item =
"extract_x_spec_f2e11467_fff9_4f11_8f3a_125336caf22e"]
#[gillian::decl::specification]
#[gillian::decl::pred_ins = "1"]
fn extract_x_spec_f2e11467_fff9_4f11_8f3a_125336caf22e<'a,
    T: Ownable>(p: &'a mut WP<T>, ret: ()) -> gilogic::RustAssertion {
    unsafe {
        gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |x, y|
                {
                    gilogic::__stubs::spec(wp_ref_mut_xy(p, x, y),
                        [{
                                    gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] ||
                                            { <&mut T as Ownable>::own(&mut (*x).v) })
                                }])
                })
    }
}
#[gillian::extract_lemma =
"extract_x_extract_lemma_182a34a1_599c_49be_91bf_0490844500cf"]
#[gillian::spec = "extract_x_spec_f2e11467_fff9_4f11_8f3a_125336caf22e"]
#[allow(unsused_variables)]
#[gillian::trusted]
fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>) {
    unreachable!()
}


#[extract_lemma(
    forall x, y.
    from { wp_ref_mut_xy(p, x, y) }
    extract { <&mut T as Ownable>::own(&mut (*y).v) }
)]
fn extract_y<'a, T: Ownable>(p: &'a mut WP<T>);

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
        let xbox = Box::new(N {
            v: x,
            o: std::ptr::null_mut(),
        });
        let ybox = Box::new(N {
            v: y,
            o: std::ptr::null_mut(),
        });

        let xptr = Box::leak(xbox) as *mut N<T>;
        let yptr = Box::leak(ybox) as *mut N<T>;

        unsafe {
            (*yptr).o = xptr;
            (*xptr).o = yptr;
        }
        WP { x: xptr, y: yptr }
    }

    #[show_safety]
    fn assign_first<'a>(&'a mut self, x: T) {
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

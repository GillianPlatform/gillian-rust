//@check-pass
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

// #[gilogic::macros::lemma]
// #[gilogic::macros::specification(
//     forall p: & mut WP<T>, x, y, m, new_new_model.
//         requires {
//             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, m, (x, y))
//         }
//         exists mx.
//         ensures  {
//             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, mx, ())
//             * (m == (m.0, mx))
//             * gilogic::__stubs::wand(
//                 gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, new_new_model, ()),
//                 gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, (m.0, new_new_model), (x, y),)
//             )
//         }
// )]
// #[gillian::args_deferred]
// #[gillian::timeless]
// fn extract_x_2_proof<'a, T: Ownable>(p: &'a mut WP<T>) {
//     ::gilogic::package!(
//         gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, new_new_model, ()),
//         gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, (m.0, new_new_model), (x, y),)
//     );
// }

// #[lemma]
// #[specification(
//     forall p x y.
//     requires {
//         no_proph::FrozenOwn::just_ref_mut_points_to(p, (x, y))
//     }
//     ensures {
//         no_proph::FrozenOwn::just_ref_mut_points_to(&mut (*x).v, ())
//         * wand(
//             gilogic::no_proph::FrozenOwn::just_ref_mut_points_to(&mut (*x).v, ()),
//             gilogic::no_proph::FrozenOwn::just_ref_mut_points_to(p, (x, y))
//         )
//     }
// )]

#[extract_lemma(
    forall x, y.
    from { wp_ref_mut_xy(p, (x, y)) }
    extract { <&mut T as Ownable>::own(&mut (*x).v) }
)]
fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>);

#[extract_lemma(
    forall x, y.
    from { wp_ref_mut_xy(p, (x, y)) }
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

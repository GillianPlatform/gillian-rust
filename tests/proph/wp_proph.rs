//@check-pass
#![feature(concat_idents)]

extern crate creusillian;
extern crate gilogic;

use gilogic::{
    macros::{assertion, extract_lemma, predicate, specification, with_freeze_lemma},
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

#[with_freeze_lemma(
    lemma_name = freeze_xy,
    predicate_name = wp_ref_mut_xy,
    frozen_variables = [x, y],
)]
impl<T: Ownable> Ownable for WP<T> {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|x: *mut N<T>, y: *mut N<T>| wp(self, x, y, model))
    }
}

// #[cfg(gillian)]
// #[gillian::no_translate]
// fn extract_x___proof<'a, T: Ownable>(p: &'a mut WP<T>) {
//     unsafe {
//         #[gillian::decl::lemma]
//         #[gillian::timeless]
//         #[gillian::magic_closure]
//         #[gillian::spec = "extract_x___proof_spec_e340188d_4a2d_4df3_ba58_82d06e40814b"]
//         #[gillian::decl::pred_ins = "3"]
//         |p: &'a mut WP<T>, x: *mut N<T>, y: *mut N<T>, m, mx, new_new_model| {
//                     let _ = (#[gillian::no_translate]
//                     #[gillian::item = "extract_x___proof_spec_e340188d_4a2d_4df3_ba58_82d06e40814b"]
//                     #[gillian::decl::specification]
//                     #[gillian::decl::pred_ins = "1"]
//                     || -> gilogic::RustAssertion {
//                         unsafe {
//                             gilogic::__stubs::spec(
//                                 gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                                     p,
//                                     m,
//                                     (x, y),
//                                 ),
//                                 [{
//                                     gilogic::__stubs::instantiate_lvars(
//                                         #[gillian::no_translate]
//                                         || {
//                                             gilogic::__stubs::star(gilogic::__stubs::star(gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*x).v,
//                                                                                 mx, ()),
//                                                                             gilogic::__stubs::pure(gilogic::__stubs::equal(m,
//                                                                                     (mx, m.1)))),
//                                                                         gilogic::__stubs::wand(gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*x).v,
//                                                                                 new_new_model, ()),
//                                                                             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p,
//                                                                                 (new_new_model, m.1), (x, y))))
//                                         },
//                                     )
//                                 }],
//                             )
//                         }
//                     });
//                     gilogic::__stubs::package(
//                         gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                             &mut (*x).v,
//                             new_new_model,
//                             (),
//                         ),
//                         gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                             p,
//                             (new_new_model, m.1),
//                             (x, y),
//                         ),
//                     );
//         }
//     };
// }
// #[cfg(gillian)]
// #[rustc_diagnostic_item = "extract_x_spec_0eb6d6cf_b515_4792_934a_ac01a89865b8"]
// #[gillian::decl::specification]
// #[gillian::decl::pred_ins = "1"]
// fn extract_x_spec_0eb6d6cf_b515_4792_934a_ac01a89865b8<'a, T: Ownable>(
//     p: &'a mut WP<T>,
//     ret: Prophecy<T::RepresentationTy>,
// ) -> gilogic::RustAssertion {
//     unsafe {
//         gilogic::__stubs::instantiate_lvars(
//             #[gillian::no_translate]
//             |x: *mut N<T>, y: *mut N<T>, m| {
//                 gilogic::__stubs::spec(
//                     wp_ref_mut_xy(p, m, (x, y)),
//                     [{
//                         gilogic::__stubs::instantiate_lvars(
//                             #[gillian::no_translate]
//                             |mx: (T::RepresentationTy, T::RepresentationTy),
//                              __OLD_PROPH_VAL,
//                              __NEW_PROPH_VAL,
//                              __NEW_PROPH_OLD_VAL| {
//                                 gilogic::__stubs::star(
//                                     gilogic::__stubs::star(
//                                         gilogic::__stubs::star(
//                                             gilogic::__stubs::star(
//                                                 gilogic::__stubs::pure(gilogic::__stubs::equal(
//                                                     __OLD_PROPH_VAL,
//                                                     m.0,
//                                                 )),
//                                                 gilogic::__stubs::pure(gilogic::__stubs::equal(
//                                                     __NEW_PROPH_VAL,
//                                                     mx.1,
//                                                 )),
//                                             ),
//                                             gilogic::__stubs::pure(gilogic::__stubs::equal(
//                                                 __NEW_PROPH_OLD_VAL,
//                                                 mx.0,
//                                             )),
//                                         ),
//                                         gilogic::__stubs::observation(
//                                             (gilogic::__stubs::expr_eq(
//                                                 m.1,
//                                                 ((__NEW_PROPH_VAL, __OLD_PROPH_VAL.1)),
//                                             )) && (gilogic::__stubs::expr_eq(
//                                                 m.0,
//                                                 ((__NEW_PROPH_OLD_VAL, __OLD_PROPH_VAL.1)),
//                                             )),
//                                         ),
//                                     ),
//                                     Ownable::own(
//                                         gilogic::prophecies::Prophecised::with_prophecy(
//                                             &mut (*x).v,
//                                             ret,
//                                         ),
//                                         mx,
//                                     ),
//                                 )
//                             },
//                         )
//                     }],
//                 )
//             },
//         )
//     }
// }
// #[gillian::spec = "extract_x_spec_0eb6d6cf_b515_4792_934a_ac01a89865b8"]
// #[allow(unsused_variables)]
// #[gillian::trusted]
// fn extract_x<'a, T: Ownable>(p: &'a mut WP<T>) -> Prophecy<T::RepresentationTy> {
//     unreachable!()
// }

// #[extract_lemma(
//     forall x, y.
//     model m.
//     extract model mx.
//     from { wp_ref_mut_xy(p, m, (x, y)) }
//     extract { Ownable::own(&mut (*y).v, mx) }
//     prophecise { (m.0, mx) }
// )]
// fn extract_y<'a, T: Ownable>(p: &'a mut WP<T>) -> Prophecy<T::RepresentationTy>;

#[gilogic::macros::lemma]
#[gilogic::macros::specification(
    forall p: & mut WP<T>, x, y, m, new_new_model.
        requires {
            gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, m, (x, y))
        }
        exists mx.
        ensures  {
            gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, mx, ())
            * (m == (m.0, mx))
            * gilogic::__stubs::wand(
                gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, new_new_model, ()),
                gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, (m.0, new_new_model), (x, y),)
            )
        }
)]
#[gillian::args_deferred]
#[gillian::timeless]
fn extract_x_2_proof<'a, T: Ownable>(p: &'a mut WP<T>) {
    ::gilogic::package!(
        gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(&mut (*y).v, new_new_model, ()),
        gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, (m.0, new_new_model), (x, y),)
    );
}

// #[cfg(gillian)]
// #[gillian::timeless]
// #[gillian::decl::lemma]
// #[gillian::args_deferred]
// #[gillian::spec = "extract_y___proof_spec_fefa9588_4d38_4a47_ac0f_88a07cd5e88d"]
// fn extract_y___proof<'a, T: Ownable>(p: &'a mut WP<T>) {
//     gilogic::__stubs::instantiate_lvars(
//         #[gillian::no_translate]
//         |x, y, m, new_new_model| unsafe {
//             let omgomg = (#[gillian::no_translate]
//             #[gillian::item = "extract_y___proof_spec_fefa9588_4d38_4a47_ac0f_88a07cd5e88d"]
//             #[gillian::decl::specification]
//             #[gillian::decl::pred_ins = "1"]
//             #[gillian::magic_closure]
//             |p: &'a mut WP<T>, x, y, m, new_new_model| -> gilogic::RustAssertion {
//                 unsafe {
//                     gilogic::__stubs::spec(
//                         gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(p, m, (x, y)),
//                         [{
//                             gilogic::__stubs::instantiate_lvars(
//                                 #[gillian::no_translate]
//                                 |mx| {
//                                     gilogic::__stubs::star(
//                                         gilogic::__stubs::star(
//                                             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                                                 &mut (*y).v,
//                                                 mx,
//                                                 (),
//                                             ),
//                                             gilogic::__stubs::pure(gilogic::__stubs::equal(
//                                                 m,
//                                                 (m.0, mx),
//                                             )),
//                                         ),
//                                         gilogic::__stubs::wand(
//                                             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                                                 &mut (*y).v,
//                                                 new_new_model,
//                                                 (),
//                                             ),
//                                             gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                                                 p,
//                                                 (m.0, new_new_model),
//                                                 (x, y),
//                                             ),
//                                         ),
//                                     )
//                                 },
//                             )
//                         }],
//                     )
//                 }
//             })(p, x, y, m, new_new_model);
//             gilogic::__stubs::package(
//                 gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                     &mut (*y).v,
//                     new_new_model,
//                     (),
//                 ),
//                 gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(
//                     p,
//                     (m.0, new_new_model),
//                     (x, y),
//                 ),
//             );
//         },
//     )
// }
#[cfg(gillian)]
#[rustc_diagnostic_item = "extract_y_spec_90fd0a4d_a5a3_4f5f_84da_70177e259d8d"]
#[gillian::decl::specification]
#[gillian::decl::pred_ins = "1"]
fn extract_y_spec_90fd0a4d_a5a3_4f5f_84da_70177e259d8d<'a, T: Ownable>(
    p: &'a mut WP<T>,
    ret: Prophecy<T::RepresentationTy>,
) -> gilogic::RustAssertion {
    unsafe {
        gilogic::__stubs::instantiate_lvars(
            #[gillian::no_translate]
            |x, y, m| {
                gilogic::__stubs::spec(
                    wp_ref_mut_xy(p, m, (x, y)),
                    [{
                        gilogic::__stubs::instantiate_lvars(
                            #[gillian::no_translate]
                            |mx: (T::RepresentationTy, T::RepresentationTy),
                             __OLD_PROPH_VAL,
                             __NEW_PROPH_VAL,
                             __NEW_PROPH_OLD_VAL| {
                                gilogic::__stubs::star(
                                    gilogic::__stubs::star(
                                        gilogic::__stubs::star(
                                            gilogic::__stubs::star(
                                                gilogic::__stubs::pure(gilogic::__stubs::equal(
                                                    __OLD_PROPH_VAL,
                                                    m.0,
                                                )),
                                                gilogic::__stubs::pure(gilogic::__stubs::equal(
                                                    __NEW_PROPH_VAL,
                                                    mx.1,
                                                )),
                                            ),
                                            gilogic::__stubs::pure(gilogic::__stubs::equal(
                                                __NEW_PROPH_OLD_VAL,
                                                mx.0,
                                            )),
                                        ),
                                        gilogic::__stubs::observation(
                                            (gilogic::__stubs::expr_eq(
                                                m.1,
                                                ((__OLD_PROPH_VAL.0, __NEW_PROPH_VAL)),
                                            )) && (gilogic::__stubs::expr_eq(
                                                m.0,
                                                ((__OLD_PROPH_VAL.0, __NEW_PROPH_OLD_VAL)),
                                            )),
                                        ),
                                    ),
                                    Ownable::own(
                                        gilogic::prophecies::Prophecised::with_prophecy(
                                            &mut (*y).v,
                                            ret,
                                        ),
                                        mx,
                                    ),
                                )
                            },
                        )
                    }],
                )
            },
        )
    }
}
#[gillian::spec = "extract_y_spec_90fd0a4d_a5a3_4f5f_84da_70177e259d8d"]
#[allow(unsused_variables)]
#[gillian::trusted]
fn extract_y<'a, T: Ownable>(p: &'a mut WP<T>) -> Prophecy<T::RepresentationTy> {
    ::core::panicking::panic("internal error: entered unreachable code")
}

impl<T: Ownable> WP<T> {
    #[creusillian::ensures(((ret@).0 == x@) && ((ret@).1 == y@))]
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

    // #[creusillian::ensures(((^self@).0 == x@) && ((*self@).1 == (^self@).1))]
    // fn assign_first(&mut self, x: T) {
    //     unsafe {
    //         (*self.x).v = x;
    //         mutref_auto_resolve!(self);
    //     }
    // }

    // #[creusillian::ensures(*ret == (*self@).0 && ^ret@ == (^self@).0 && (^self@).1 == (*self@).1)]
    // fn first_mut<'a>(&'a mut self) -> &'a mut T {
    //     unsafe {
    //         freeze_xy(self);
    //         let ret = &mut (*self.x).v;
    //         let proph = extract_x(self);
    //         ret.with_prophecy(proph)
    //     }
    // }

    // #[creusillian::ensures(*ret == (*self@).1 && ^ret@ == (^self@).1 && (^self@).0 == (*self@).0)]
    // fn second_mut<'a>(&'a mut self) -> &'a mut T {
    //     unsafe {
    //         freeze_xy(self);
    //         let ret = &mut (*self.y).v;
    //         let proph = extract_y(self);
    //         ret.with_prophecy(proph)
    //     }
    // }
}

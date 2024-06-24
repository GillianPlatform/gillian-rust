use crate as gilogic;
use crate::tys::RustAssertion;
use gilogic::macros::assertion;

macro_rules! unreachable {
    ($x:expr) => {
        panic!()
    };
    () => {
        panic!()
    };
}

/*
Here's an idea:
I could have a trait MutBorrow, which can be opened, closed etc...
And there would be functions between MutBorrows:
-> Splits which can split borrows in bits
-> pull, which can pull existentials from a borrow.

Not sure how that would work, but it'd certainly be a nicer interface.
*/

#[allow(non_snake_case)]
pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::pcy::ownable::representation_ty"]
    type RepresentationTy;

    #[rustc_diagnostic_item = "gillian::pcy::ownable::own"]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: Self::RepresentationTy) -> RustAssertion;

    // #[rustc_diagnostic_item = "gillian::pcy::ownable::ref_mut_inner"]
    // #[gillian::decl::pred_ins = "0"]
    // fn ref_mut_inner(&mut self) -> RustAssertion {
    //     unreachable!("Implemented in GIL")
    // }

    // #[rustc_diagnostic_item = "gillian::unfold::pcy::ownable::ref_mut_inner"]
    // fn ref_mut_inner_____unfold(&mut self) -> RustAssertion {
    //     unreachable!("Implemented in GIL")
    // }

    // #[rustc_diagnostic_item = "gillian::fold::pcy::ownable::ref_mut_inner"]
    // fn ref_mut_inner_____fold(&mut self) -> RustAssertion {
    //     unreachable!("Implemented in GIL")
    // }
}

macro_rules! own_int {
    ($t:ty) => {
        impl Ownable for $t {
            type RepresentationTy = $t;

            #[cfg(gillian)]
            #[gillian::decl::predicate]
            #[gillian::decl::pred_ins = "0"]
            fn own(self, model: $t) -> RustAssertion {
                gilogic::__stubs::defs([assertion!(($t::MIN <= self) * (self <= $t::MAX) * (self == model))])
            }

            #[cfg(not(gillian))]
            fn own(self, _model: $t) -> RustAssertion {
                unreachable!("")
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        own_int!($t);
        own_int!($($ts),+);
    };
}
use gilogic::macros::borrow;

// impl<T : Ownable> &mut T {
//     #[borrow]
//     #[rustc_allow_incoherent_impl]
//     fn mut_ref_inner(self) -> RustAssertion {
//         assertion!(|v, repr| (self -> v) * v.own(repr) * controller(self.prophecy(), repr))
//     }
// }
//

#[borrow]
fn mut_ref_inner_proph<'a, U: Ownable>(this: In<&'a mut U>) -> RustAssertion {
    assertion!(|v, repr| (this -> v) * v.own(repr) * controller(this.prophecy(), repr))
}

// #[borrow]
// fn wp_ref_mut_inner_xy<'a, T: Ownable>(p: In<&'a mut WP<T>>, x: *mut N<T>, y: *mut N<T>) {
//     assertion!(|v_x: T, v_y: T, v_x_m: T::RepresentationTy, v_y_m: T::RepresentationTy|
//         (p -> WP { x, y }) *
//         wp(WP { x, y }, x, y, (v_x_m, v_y_m)) * controller(p.prophecy(), (v_x_m, v_y_m))
//     )
// }

impl<T: Ownable> Ownable for &mut T {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);
    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: (T::RepresentationTy, T::RepresentationTy)) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(|a, b| (model == (a, b))
            * mut_ref_inner_proph(self)
            * observer(self.prophecy(), a)
            * (self.prophecy().value() == b))])
    }

    #[cfg(not(gillian))]
    fn own(self, _model: (T::RepresentationTy, T::RepresentationTy)) -> RustAssertion {
        unreachable!("")
    }
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    type RepresentationTy = (T::RepresentationTy, U::RepresentationTy);

    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: (T::RepresentationTy, U::RepresentationTy)) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(|l, r| (model == (l, r))
            * self.0.own(l)
            * self.1.own(r))])
    }

    #[cfg(not(gillian))]
    fn own(self, _model: (T::RepresentationTy, U::RepresentationTy)) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

impl<T: Ownable> Ownable for Option<T> {
    type RepresentationTy = Option<T::RepresentationTy>;

    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: Option<T::RepresentationTy>) -> RustAssertion {
        gilogic::__stubs::defs([
            assertion!((self == None) * (model == None)),
            assertion!(|ax: T, repr: _| (self == Some(ax))
                * <T as Ownable>::own(ax, repr)
                * (model == Some(repr))),
        ])
    }

    #[cfg(not(gillian))]
    fn own(self, _model: Option<T::RepresentationTy>) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

impl Ownable for () {
    type RepresentationTy = ();

    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: ()) -> RustAssertion {
        gilogic::__stubs::defs([assertion!((self == ()) * (self == model))])
    }

    #[cfg(not(gillian))]
    fn own(self, _model: ()) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

pub trait Prophecised {
    type ProphecyTy;

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::get_prophecy"]
    fn prophecy(self) -> Self::ProphecyTy;

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::set_prophecy"]
    fn with_prophecy(self, pcy: Self::ProphecyTy) -> Self;

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::prophecy_auto_update"]
    fn prophecy_auto_update(self);

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::resolve"]
    fn prophecy_resolve(self);
}

impl<T> Prophecised for &mut T
where
    T: Ownable,
{
    type ProphecyTy = Prophecy<T::RepresentationTy>;

    fn prophecy(self) -> Prophecy<T::RepresentationTy> {
        unreachable!("Implemented in GIL")
    }

    fn with_prophecy(self, _pcy: Prophecy<T::RepresentationTy>) -> Self {
        unreachable!("Implemented in GIL")
    }

    fn prophecy_auto_update(self) {
        unreachable!("Implemented in GIL")
    }

    fn prophecy_resolve(self) {
        unreachable!("Implemented in GIL")
    }
}

#[derive(Clone, Copy)]
pub struct Prophecy<T: ?Sized>(core::marker::PhantomData<T>);

impl<T> Prophecy<T> {
    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::get_value"]
    pub fn value(self) -> T {
        unreachable!("Implemented in GIL")
    }

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::resolve"]
    pub fn resolve(self) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::assign"]
    pub fn assign(self, _v: T) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::assign_proph"]
    pub fn assign_proph(self, _v: Prophecy<T>) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::rebased"]
    pub fn rebased(self) -> Self {
        unreachable!("Implemented in GIL")
    }
}

impl<T, U> Prophecy<(T, U)> {
    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::0"]
    pub fn field_0(self) -> Prophecy<T> {
        unreachable!("Implemented in GIL")
    }

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::1"]
    pub fn field_1(self) -> Prophecy<U> {
        unreachable!("Implemented in GIL")
    }
}

#[gillian::no_translate]
#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::controller"]
pub fn controller<T>(_x: Prophecy<T>, _v: T) -> RustAssertion {
    unreachable!("")
}

#[gillian::no_translate]
#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::observer"]
pub fn observer<T>(_x: Prophecy<T>, _v: T) -> RustAssertion {
    unreachable!("")
}

#[macro_export]
macro_rules! mutref_auto_resolve {
    ($x: expr) => {
        $x.prophecy_auto_update();
        $x.prophecy_resolve();
    };
}

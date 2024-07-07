use crate as gilogic;
use crate::tys::RustAssertion;
use gilogic::macros::{assertion, borrow, lemma, predicate, specification};

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
            #[predicate]
            fn own(self, model: $t) {
                assertion!(($t::MIN <= self) * (self <= $t::MAX) * (self == model))
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

#[borrow]
fn mut_ref_inner_proph<'a, U: Ownable>(this: In<&'a mut U>) -> RustAssertion {
    assertion!(|v, repr| (this -> v) * v.own(repr) * controller(this.prophecy(), repr))
}

impl<T: Ownable> Ownable for &mut T {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);
    #[cfg(gillian)]
    #[predicate]
    fn own(self, model: (T::RepresentationTy, T::RepresentationTy)) {
        assertion!(|a, b| (model == (a, b))
            * mut_ref_inner_proph(self)
            * observer(self.prophecy(), a)
            * (self.prophecy().value() == b))
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
    #[predicate]
    fn own(self, model: (T::RepresentationTy, U::RepresentationTy)) {
        assertion!(|l, r| (model == (l, r)) * self.0.own(l) * self.1.own(r))
    }

    #[cfg(not(gillian))]
    fn own(self, _model: (T::RepresentationTy, U::RepresentationTy)) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

impl<T: Ownable> Ownable for Option<T> {
    type RepresentationTy = Option<T::RepresentationTy>;

    #[cfg(gillian)]
    #[predicate]
    fn own(self, model: Option<T::RepresentationTy>) {
        assertion!((self == None) * (model == None));
        assertion!(|ax: T, repr: _| (self == Some(ax))
            * <T as Ownable>::own(ax, repr)
            * (model == Some(repr)))
    }

    #[cfg(not(gillian))]
    fn own(self, _model: Option<T::RepresentationTy>) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

impl Ownable for () {
    type RepresentationTy = ();

    #[cfg(gillian)]
    #[predicate]
    fn own(self, model: ()) -> RustAssertion {
        assertion!((self == ()) * (self == model))
    }

    #[cfg(not(gillian))]
    fn own(self, _model: ()) -> RustAssertion {
        unreachable!("Implemented in GIL");
    }
}

pub trait Prophecised<P> {
    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::get_prophecy"]
    fn prophecy(self) -> Prophecy<P>;

    #[gillian::no_translate]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::set_prophecy"]
    fn with_prophecy(self, pcy: Prophecy<P>) -> Self;
}

impl<T> Prophecised<T::RepresentationTy> for &mut T
where
    T: Ownable,
{
    fn prophecy(self) -> Prophecy<T::RepresentationTy> {
        unreachable!("Implemented in GIL")
    }

    fn with_prophecy(self, _pcy: Prophecy<T::RepresentationTy>) -> Self {
        unreachable!("Implemented in GIL")
    }
}

#[specification(forall v, a, r.
    requires {
        (p -> v) * v.own(r) *
        observer(p.prophecy(), a) *
        controller(p.prophecy(), a)
    }
    ensures {
        (p -> v) * v.own(r) *
        observer(p.prophecy(), r) *
        controller(p.prophecy(), r)
}
)]
#[gillian::timeless]
pub fn prophecy_auto_update<T: Ownable>(p: &mut T) {
    let _ = p;
    unreachable!();
}

#[specification(forall m.
    requires { p.own(m) }
    ensures { $(m.0 == m.1)$ }
)]
#[gillian::timeless]
pub fn prophecy_resolve<T: Ownable>(p: &mut T) {
    let _ = p;
    unreachable!();
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::check_obs_sat"]
pub fn check_obs_sat() {
    unreachable!();
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
        gilogic::prophecies::check_obs_sat();
        gilogic::prophecies::prophecy_auto_update($x);
        gilogic::prophecies::prophecy_resolve($x);
    };
}

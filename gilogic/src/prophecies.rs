use crate as gilogic;
use crate::tys::RustAssertion;
use gilogic::macros::*;

macro_rules! unreachable {
    ($x:expr) => {
        panic!()
    };
    () => {
        panic!()
    };
}

#[allow(non_snake_case)]
pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::pcy::ownable::representation_ty"]
    type RepresentationTy;

    #[rustc_diagnostic_item = "gillian::pcy::ownable::own"]
    #[gillian::decl::pred_ins = "0"]
    fn own(self, model: Self::RepresentationTy) -> RustAssertion;
}

macro_rules! own_int {
    ($t:ty) => {
        impl Ownable for $t {
            type RepresentationTy = $t;


            #[predicate]
            fn own(self, model: $t) {
                assertion!(($t::MIN <= self) * (self <= $t::MAX) * (self == model))
            }

        }
    };

    ($t:ty, $($ts:ty),+) => {
        own_int!($t);
        own_int!($($ts),+);
    };
}

/// # Safety
/// Must only be derived by the Gillian-Rust provided macros!!
pub unsafe trait FrozenOwn<T: core::marker::Tuple + Sized>: Ownable + Sized {
    #[gillian::decl::pred_ins = "0"]
    fn frozen_own(this: Self, repr: Self::RepresentationTy, frozen: T) -> RustAssertion;

    /// The body of a mutable borrow
    #[predicate]
    fn just_ref_mut_points_to(
        this: In<&mut Self>,
        model: Self::RepresentationTy,
        frozen: T,
    ) -> RustAssertion {
        assertion!(|v| (this -> v) * Self::frozen_own(v, model, frozen))
    }

    #[predicate]
    #[gillian::borrow]
    fn mut_ref_inner_frozen(this: In<&mut Self>, frozen: T) -> RustAssertion {
        assertion!(
            |v, repr| (this -> v) * controller(this.prophecy(), repr) * Self::frozen_own(v, repr, frozen)
        )
    }

    #[predicate]
    fn mut_ref_own_frozen(
        this: In<&mut Self>,
        model: (Self::RepresentationTy, Self::RepresentationTy),
        frozen: T,
    ) -> RustAssertion {
        assertion!(|a, b| (model == (a, b))
            * Self::mut_ref_inner_frozen(this, frozen)
            * observer(this.prophecy(), a)
            * (this.prophecy().value() == b))
    }
}

unsafe impl<T> FrozenOwn<()> for T
where
    T: Ownable,
{
    #[predicate]
    fn frozen_own(
        this: In<Self>,
        repr: <Self as Ownable>::RepresentationTy,
        frozen: (),
    ) -> RustAssertion {
        assertion!(this.own(repr) * (frozen == ()))
    }
}

impl<T: Ownable> Ownable for &mut T {
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);
    #[predicate]
    fn own(self, model: (T::RepresentationTy, T::RepresentationTy)) {
        assertion!(<T as FrozenOwn<()>>::mut_ref_own_frozen(self, model, ()))
    }
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    type RepresentationTy = (T::RepresentationTy, U::RepresentationTy);

    #[predicate]
    fn own(self, model: (T::RepresentationTy, U::RepresentationTy)) {
        assertion!(|l, r| (model == (l, r)) * self.0.own(l) * self.1.own(r))
    }
}

impl<T: Ownable> Ownable for Option<T> {
    type RepresentationTy = Option<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Option<T::RepresentationTy>) {
        assertion!((self == None) * (model == None));
        assertion!(|ax: T, repr: _| (self == Some(ax))
            * <T as Ownable>::own(ax, repr)
            * (model == Some(repr)))
    }
}

impl Ownable for () {
    type RepresentationTy = ();

    #[predicate]
    fn own(self, model: ()) -> RustAssertion {
        assertion!((self == ()) * (self == model))
    }
}

impl Ownable for bool {
    type RepresentationTy = bool;

    #[predicate]
    fn own(self, model: bool) -> RustAssertion {
        assertion!((self == model))
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

#[specification(forall v, a, r, frozen.
    requires {
        (p -> v) * <T as FrozenOwn<A>>::frozen_own(v, r, frozen) *
        observer(p.prophecy(), a) *
        controller(p.prophecy(), a)
    }
    ensures {
        (p -> v) * <T as FrozenOwn<A>>::frozen_own(v, r, frozen) *
        observer(p.prophecy(), r) *
        controller(p.prophecy(), r)
}
)]
#[gillian::timeless]
pub fn prophecy_auto_update<A: core::marker::Tuple, T: FrozenOwn<A> + Ownable>(p: &mut T) {
    let _ = p;
    unreachable!();
}

#[specification(forall m, frozen.
    requires { T::mut_ref_own_frozen(p, m, frozen) }
    ensures { $(m.0 == m.1)$ }
)]
#[gillian::timeless]
pub fn prophecy_resolve<A: core::marker::Tuple, T: FrozenOwn<A> + Ownable>(p: &mut T) {
    let _ = p;
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::check_obs_sat"]
pub fn check_obs_sat() {
    unreachable!();
}

#[specification(
    forall m.
    requires { p.own(m) }
    exists frozen.
    ensures { T::mut_ref_own_frozen(p, m, frozen) }
)]
#[gillian::timeless]
pub fn freeze_params<A: core::marker::Tuple, T: FrozenOwn<A> + Ownable>(p: &mut T) {
    let _ = p;
    unreachable!()
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
        mutref_auto_resolve!($x, ());
    };
    ($x: expr, $t: ty) => {
        gilogic::prophecies::check_obs_sat();
        gilogic::prophecies::prophecy_auto_update::<$t, _>($x);
        gilogic::prophecies::prophecy_resolve::<$t, _>($x);
    };
}

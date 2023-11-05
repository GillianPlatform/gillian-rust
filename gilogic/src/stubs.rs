use core::ptr::NonNull;

use super::tys::{RustAssertion, RustFormula};

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::lang::unfold"]
pub fn unfold(_args: &[&dyn core::any::Any]) {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::lang::lvar"]
pub fn lvar<T>(_name: &'static str) -> T {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::emp"]
pub fn emp() -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::star"]
pub fn star(_: RustAssertion, _: RustAssertion) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::pred::defs"]
pub fn defs<const N: usize>(_: [RustAssertion; N]) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::equal"]
pub fn equal<T>(_: T, _: T) -> RustFormula {
    unreachable!()
}

// less and less_eq should be only for numbers

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::less_eq"]
pub fn less_eq<T>(_: T, _: T) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::less"]
pub fn less<T>(_: T, _: T) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::neg"]
pub fn neg(_: RustFormula) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::pure"]
pub fn pure(_: RustFormula) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::observation"]
pub fn observation(_: RustFormula) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::forall"]
pub fn forall<T, F: Fn(T) -> RustFormula>(_: F) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::and"]
pub fn and(_: RustFormula, _: RustFormula) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::implication"]
pub fn implication(_: RustFormula, _: RustFormula) -> RustFormula {
    unreachable!()
}

pub trait PointsTo<T>: Sized {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::points_to"]
    fn points_to(self, _: T) -> RustAssertion {
        unreachable!()
    }
}

impl<T> PointsTo<T> for &T {}
impl<T> PointsTo<T> for &mut T {}
impl<T> PointsTo<T> for *const T {}
impl<T> PointsTo<T> for *mut T {}
impl<T> PointsTo<T> for Box<T> {}
impl<T> PointsTo<T> for NonNull<T> {}

pub trait PointsToSlice<T>: Sized {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::points_to_slice"]
    fn points_to_slice(self, _sz: usize, _content: super::Seq<T>) -> RustAssertion {
        unreachable!()
    }
}

impl<T> PointsToSlice<T> for *mut T {}

pub trait PointsToMaybeUninit<T>: Sized {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::uninit"]
    fn uninit(self) -> RustAssertion {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::many_uninits"]
    fn many_uninits(self, _: usize) -> RustAssertion {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::maybe_uninit"]
    fn maybe_uninit(self, _: Option<T>) -> RustAssertion {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::asrt::many_maybe_uninits"]
    fn many_maybe_uninits(self, _len: usize, _: super::Seq<Option<T>>) -> RustAssertion {
        unreachable!()
    }
}
impl<T> PointsToMaybeUninit<T> for *const T {}
impl<T> PointsToMaybeUninit<T> for *mut T {}

pub trait InstantiateLVar {
    fn instantiate_lvar() -> Self;
}

impl<T> InstantiateLVar for T
where
    T: core::any::Any,
{
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::logic::instantiate_lvar"]
    fn instantiate_lvar() -> Self {
        unreachable!()
    }
}

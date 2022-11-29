use core::ptr::NonNull;

use super::tys::{RustAssertion, RustFormula};

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

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::pure"]
pub fn pure(_: RustFormula) -> RustAssertion {
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

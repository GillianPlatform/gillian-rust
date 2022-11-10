use super::tys::{RustAssertion, RustFormula};

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::emp"]
pub fn emp() -> RustAssertion {
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
    fn points_to(self, _: T) -> bool {
        unreachable!()
    }
}

impl<T> PointsTo<T> for &T {}
impl<T> PointsTo<T> for &mut T {}
impl<T> PointsTo<T> for *const T {}
impl<T> PointsTo<T> for *mut T {}

pub fn star(_: RustAssertion, _: RustAssertion) -> RustAssertion {
    unreachable!()
}

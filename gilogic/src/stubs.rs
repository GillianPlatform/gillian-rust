use super::tys::{RustAssertion, RustFormula};

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::predicate::in"]
pub struct In<T>(std::marker::PhantomData<T>);

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::emp"]
pub fn emp() -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::formula::emp"]
pub fn equal<T>(_: T, _: T) -> RustFormula {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::pure"]
pub fn pure(_: RustFormula) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::asrt::points_to"]
pub fn points_to<T>(_: &T, _: T) -> RustAssertion {
    unreachable!()
}

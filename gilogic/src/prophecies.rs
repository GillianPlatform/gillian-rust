use crate::RustAssertion;

#[derive(Clone, Copy)]
pub struct Prophecy<T: ?Sized>(core::marker::PhantomData<T>);

impl<T> Prophecy<T> {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::get_value"]
    pub fn value(self) -> T {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::resolve"]
    pub fn resolve(self) {
        unreachable!()
    }
}

impl<T, U> Prophecy<(T, U)> {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::0"]
    pub fn field_0(self) -> Prophecy<T> {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::1"]
    pub fn field_1(self) -> Prophecy<U> {
        unreachable!()
    }
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::controller"]
pub fn controller<T>(_x: Prophecy<T>, _v: T) -> RustAssertion {
    unreachable!()
}

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::prophecy::observer"]
pub fn observer<T>(_x: Prophecy<T>, _v: T) -> RustAssertion {
    unreachable!()
}

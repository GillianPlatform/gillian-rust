use crate::RustAssertion;

#[derive(Clone, Copy)]
pub struct Prophecy<T: ?Sized>(core::marker::PhantomData<T>);

impl<T> Prophecy<T> {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::get_value"]
    pub fn value(self) -> T {
        unreachable!("Implemented in GIL")
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::resolve"]
    pub fn resolve(self) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::assign"]
    pub fn assign(self, _v: T) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::assign_proph"]
    pub fn assign_proph(self, _v: Prophecy<T>) {
        unreachable!("Implemented in GIL")
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::rebased"]
    pub fn rebased(self) -> Self {
        unreachable!("Implemented in GIL")
    }
}

impl<T, U> Prophecy<(T, U)> {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::0"]
    pub fn field_0(self) -> Prophecy<T> {
        unreachable!("Implemented in GIL")
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::prophecy::field::2::1"]
    pub fn field_1(self) -> Prophecy<U> {
        unreachable!("Implemented in GIL")
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

#[allow(unused_imports)]
use crate as gilogic;
#[allow(unused_imports)]
use crate::macros::*;
use crate::RustAssertion;

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
    #[rustc_diagnostic_item = "gillian::ownable::own"]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion;

    #[rustc_diagnostic_item = "gillian::unfold::own::open"]
    fn own_____unfold(&mut self) {
        unreachable!("Implemented in GIL")
    }

    #[rustc_diagnostic_item = "gillian::fold::own::close"]
    fn own_____fold(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

macro_rules! int_ownable {
    ($t:ty) => {
        impl Ownable for $t {

            #[cfg(gillian)]
            #[gillian::decl::predicate]
            #[gillian::decl::pred_ins = "0"]
            fn own(self) -> RustAssertion {
                gilogic::__stubs::defs([assertion!(($t::MIN <= self) * (self <= $t::MAX))])
            }

            #[cfg(not(gillian))]
            fn own(self) -> RustAssertion {
                unreachable!("")
            }

        }
    };

    ($t:ty, $($ts:ty),+) => {
        int_ownable!($t);
        int_ownable!($($ts),+);
    };
}

impl<T: Ownable> Ownable for &mut T {
    #[cfg(gillian)]
    #[gillian::borrow]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(|v| (self -> v) * v.own())])
    }

    #[cfg(not(gillian))]
    #[gillian::borrow]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

int_ownable!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(self.0.own() * self.1.own())])
    }

    #[cfg(not(gillian))]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

impl<T: Ownable> Ownable for Option<T> {
    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([
            assertion!((self == None)),
            assertion!(|ax: T| (self == Some(ax)) * <T as Ownable>::own(ax)),
        ])
    }

    #[cfg(not(gillian))]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

impl<T: Ownable> Ownable for Box<T> {
    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(|v| (self -> v) * v.own())])
    }

    #[cfg(not(gillian))]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

impl Ownable for () {
    #[cfg(gillian)]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([assertion!((self == ()))])
    }

    #[cfg(not(gillian))]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

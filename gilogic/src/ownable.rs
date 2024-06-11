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

macro_rules! stubbed_ownable {
    ($t:ty) => {
        impl Ownable for $t {

            fn own(self) -> RustAssertion {
                unreachable!("Implemented in GIL")
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        stubbed_ownable!($t);
        stubbed_ownable!($($ts),+);
    };
}

// impl<T : Ownable> &mut  T {
//     #[borrow]
//     fn mut_ref_inner(self) -> RustAssertion {
//         assertion!(|v| (self -> v) * v.own())
//     }
// }

impl<T: Ownable> Ownable for &mut T {
    #[cfg(gillian)]
    #[gillian::borrow]
    #[gillian::decl::predicate]
    #[gillian::decl::pred_ins = "0"]
    fn own(self) -> RustAssertion {
        gilogic::__stubs::defs([assertion!(|v| (self -> v) * v.own())])
        // gilogic::__stubs::defs([|v| (this -> v) * v.own()])
    }

    #[cfg(not(gillian))]
    #[gillian::borrow]
    fn own(self) -> RustAssertion {
        unreachable!("")
    }
}

stubbed_ownable!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

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
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

impl Ownable for () {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

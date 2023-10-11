use crate::RustAssertion;

#[allow(non_snake_case)]
pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::ownable::own"]
    fn own(self) -> RustAssertion;

    #[rustc_diagnostic_item = "gillian::ownable::own::open"]
    fn own_____unfold(&mut self) {
        unreachable!("Implemented in GIL")
    }

    #[rustc_diagnostic_item = "gillian::ownable::own::close"]
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

impl<T: Ownable> Ownable for &mut T {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

stubbed_ownable!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

impl<T: Ownable> Ownable for Option<T> {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL");
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

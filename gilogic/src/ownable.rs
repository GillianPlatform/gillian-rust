use crate::RustAssertion;

#[allow(non_snake_case)]
pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::ownable::own"]
    fn own(self) -> RustAssertion;

    #[rustc_diagnostic_item = "gillian::ownable::own::open"]
    fn own_____open(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }

    #[rustc_diagnostic_item = "gillian::ownable::own::close"]
    fn own_____close(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

macro_rules! own_int {
    ($t:ty) => {
        impl Ownable for $t {

            fn own(self) -> RustAssertion {
                unreachable!("Implemented in GIL")
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        own_int!($t);
        own_int!($($ts),+);
    };
}

impl<T: Ownable> Ownable for &mut T {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    fn own(self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

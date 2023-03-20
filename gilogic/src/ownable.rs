use super::RustAssertion;

pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::ownable::own"]
    fn own(self) -> RustAssertion;
}

macro_rules! own_int {
    ($t:ty) => {
        impl Ownable for $t {
            fn own(self) -> RustAssertion {
                super::__stubs::defs([
                    super::__stubs::emp()
                ])
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        own_int!($t);
        own_int!($($ts),+);
    };
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

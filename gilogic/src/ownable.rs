use super::RustAssertion;

/*
Here's an idea:
I could have a trait MutBorrow, which can be opened, closed etc...
And there would be functions between MutBorrows:
-> Splits which can split borrows in bits
-> pull, which can pull existentials from a borrow.

Not sure how that would work, but it'd certainly be a nicer interface.
*/

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

impl<T: Ownable> Ownable for &mut T {
    fn own(self) -> RustAssertion {
        super::__stubs::emp()
        // borrow!(|v| self -> v * v.own())
    }
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    fn own(self) -> RustAssertion {
        super::__stubs::defs([{ super::__stubs::star(self.0.own(), self.1.own()) }])
    }
}

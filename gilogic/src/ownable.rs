use super::RustAssertion;
use crate::prophecies::Prophecy;

/*
Here's an idea:
I could have a trait MutBorrow, which can be opened, closed etc...
And there would be functions between MutBorrows:
-> Splits which can split borrows in bits
-> pull, which can pull existentials from a borrow.

Not sure how that would work, but it'd certainly be a nicer interface.
*/

pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::own::representation_ty"]
    type RepresentationTy;

    #[rustc_diagnostic_item = "gillian::ownable::own"]
    fn own(self, model: Self::RepresentationTy) -> RustAssertion;
}

macro_rules! own_int {
    ($t:ty) => {
        impl Ownable for $t {
            type RepresentationTy = $t;

            fn own(self, _model: Self::RepresentationTy) -> RustAssertion {
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
    type RepresentationTy = (T::RepresentationTy, T::RepresentationTy);

    fn own(self, _model: Self::RepresentationTy) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

own_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    type RepresentationTy = (T::RepresentationTy, U::RepresentationTy);

    fn own(self, _model: Self::RepresentationTy) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

pub trait Prophecised {
    type ProphecyTy;

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::get_prophecy"]
    fn prophecy(self) -> Self::ProphecyTy;

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::set_prophecy"]
    fn with_prophecy(self, pcy: Self::ProphecyTy) -> Self;
}

impl<T: Ownable> Prophecised for &mut T {
    type ProphecyTy = Prophecy<T::RepresentationTy>;

    fn prophecy(self) -> Self::ProphecyTy {
        unreachable!("Implemented in GIL")
    }

    fn with_prophecy(self, _pcy: Self::ProphecyTy) -> Self {
        unreachable!("Implemented in GIL")
    }
}

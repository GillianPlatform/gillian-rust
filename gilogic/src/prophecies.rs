use crate::tys::RustAssertion;

/*
Here's an idea:
I could have a trait MutBorrow, which can be opened, closed etc...
And there would be functions between MutBorrows:
-> Splits which can split borrows in bits
-> pull, which can pull existentials from a borrow.

Not sure how that would work, but it'd certainly be a nicer interface.
*/

#[allow(non_snake_case)]
pub trait Ownable {
    #[rustc_diagnostic_item = "gillian::pcy::ownable::representation_ty"]
    type RepresentationTy;

    #[rustc_diagnostic_item = "gillian::pcy::ownable::own"]
    fn own(self, model: Self::RepresentationTy) -> RustAssertion;

    #[rustc_diagnostic_item = "gillian::pcy::ownable::ref_mut_inner"]
    fn ref_mut_inner(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }

    #[rustc_diagnostic_item = "gillian::pcy::ownable::ref_mut_inner::open"]
    fn ref_mut_inner_____open(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }

    #[rustc_diagnostic_item = "gillian::pcy::ownable::ref_mut_inner::close"]
    fn ref_mut_inner_____close(&mut self) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
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

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::prophecy_auto_update"]
    fn prophecy_auto_update(self);

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::mut_ref::resolve"]
    fn prophecy_resolve(self);
}

impl<T: Ownable> Prophecised for &mut T {
    type ProphecyTy = Prophecy<T::RepresentationTy>;

    fn prophecy(self) -> Self::ProphecyTy {
        unreachable!("Implemented in GIL")
    }

    fn with_prophecy(self, _pcy: Self::ProphecyTy) -> Self {
        unreachable!("Implemented in GIL")
    }

    fn prophecy_auto_update(self) {
        unreachable!("Implemented in GIL")
    }

    fn prophecy_resolve(self) {
        unreachable!("Implemented in GIL")
    }
}

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

#[macro_export]
macro_rules! mutref_auto_resolve {
    ($x: expr) => {
        $x.prophecy_auto_update();
        $x.prophecy_resolve();
    };
}

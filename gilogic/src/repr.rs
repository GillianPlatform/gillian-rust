use crate::prophecies::Prophecy;

use super::RustAssertion;

pub trait ShallowRepresentation {
    #[rustc_diagnostic_item = "gillian::repr::shallow_model_ty"]
    type ShallowModelTy;

    #[rustc_diagnostic_item = "gillian::repr::shallow_repr"]
    fn shallow_repr(self, model: Self::ShallowModelTy) -> RustAssertion;

    fn mut_ref_inner(
        &mut self,
        _model: (Self::ShallowModelTy, Self::ShallowModelTy),
    ) -> RustAssertion {
        unreachable!("Implemented in GIL")
    }
}

impl<T: ShallowRepresentation> ShallowRepresentation for &mut T {
    type ShallowModelTy = (T::ShallowModelTy, T::ShallowModelTy);

    fn shallow_repr(self, _model: Self::ShallowModelTy) -> RustAssertion {
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

impl<T: ShallowRepresentation> Prophecised for &mut T {
    type ProphecyTy = Prophecy<T::ShallowModelTy>;

    fn prophecy(self) -> Self::ProphecyTy {
        unreachable!("Implemented in GIL")
    }

    fn with_prophecy(self, _pcy: Self::ProphecyTy) -> Self {
        unreachable!("Implemented in GIL")
    }
}

macro_rules! shallow_repr_int {
    ($t:ty) => {
        /// This is actually useless... We generate the shallow_representation, but compilation isn't
        /// cross-crate. So for now, we also have the equivalent written in GIL directly.
        impl ShallowRepresentation for $t {
            type ShallowModelTy = $t;

            fn shallow_repr(self, model: Self::ShallowModelTy) -> RustAssertion {
                super::__stubs::defs([
                    super::__stubs::pure(
                        super::__stubs::equal(self, model)
                    )
                ])
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        shallow_repr_int!($t);
        shallow_repr_int!($($ts),+);
    };
}

shallow_repr_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

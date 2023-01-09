use super::RustAssertion;

pub trait ShallowRepresentation {
    type ShallowModelTy;

    #[rustc_diagnostic_item = "gillian::repr::shallow_repr"]
    fn shallow_repr(self, model: Self::ShallowModelTy) -> RustAssertion;
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

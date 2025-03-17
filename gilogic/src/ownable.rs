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
}

macro_rules! int_ownable {
    ($t:ty) => {
        impl Ownable for $t {

            #[predicate]
            fn own(self) {
                assertion!(($t::MIN <= self) * (self <= $t::MAX))
            }

        }
    };

    ($t:ty, $($ts:ty),+) => {
        int_ownable!($t);
        int_ownable!($($ts),+);
    };
}

/// # Safety
/// Must only be derived by the Gillian-Rust provided macros!
pub unsafe trait FrozenOwn<K: core::marker::Tuple + Sized>: Ownable + Sized {
    #[gillian::decl::pred_ins = "0"]
    fn frozen_own(this: Self, frozen: K) -> RustAssertion;

    #[predicate]
    fn just_ref_mut_points_to(this: In<&mut Self>, frozen: K) {
        assertion!(|v| (this -> v) * Self::frozen_own(v, frozen))
    }

    #[predicate]
    #[gillian::borrow]
    fn mut_ref_own_frozen(this: In<&mut Self>, frozen: K) {
        Self::just_ref_mut_points_to(this, frozen)
    }
}

unsafe impl<T> FrozenOwn<()> for T
where
    T: Ownable,
{
    #[predicate]
    fn frozen_own(this: In<Self>, frozen: ()) -> RustAssertion {
        assertion!(this.own() * (frozen == ()))
    }
}

impl<T: Ownable> Ownable for &mut T {
    #[predicate]
    fn own(self) {
        assertion!(<T as FrozenOwn<()>>::mut_ref_own_frozen(self, ()))
    }
}

int_ownable!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: Ownable, U: Ownable> Ownable for (T, U) {
    #[predicate]
    fn own(self) {
        assertion!(self.0.own() * self.1.own())
    }
}

impl<T: Ownable> Ownable for Option<T> {
    #[predicate]
    fn own(self) {
        assertion!((self == None));
        assertion!(|ax: T| (self == Some(ax)) * <T as Ownable>::own(ax))
    }
}

impl<T: Ownable> Ownable for Box<T> {
    #[predicate]
    fn own(self) {
        assertion!(|v| (self -> v) * v.own())
    }
}

impl Ownable for () {
    #[predicate]
    fn own(self) {
        assertion!((self == ()))
    }
}

#[specification(
    requires { p.own() }
    exists frozen.
    ensures { T::mut_ref_own_frozen(p, frozen) }
)]
#[gillian::timeless]
pub fn freeze_params<A: core::marker::Tuple, T: FrozenOwn<A> + Ownable>(p: &mut T) {
    let _ = p;
    unreachable!()
}

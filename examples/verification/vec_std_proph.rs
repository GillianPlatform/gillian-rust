#![feature(ptr_internals)]
#![feature(sized_type_properties)]
#![feature(allocator_api)]
extern crate gilogic;

use gilogic::{
    __stubs::PointsToMaybeUninit,
    alloc::GillianAllocator,
    macros::{assertion, ensures, lemma, predicate, requires},
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised},
    Seq,
};
use std::alloc::{Allocator, Layout};
use std::marker::PhantomData;
use std::mem::SizedTypeProperties;
use std::ptr::Unique;

pub struct TryReserveError {
    kind: TryReserveErrorKind,
}

impl From<TryReserveErrorKind> for TryReserveError {
    #[inline]
    fn from(kind: TryReserveErrorKind) -> Self {
        Self { kind }
    }
}

pub enum TryReserveErrorKind {
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,
    AllocError {
        layout: Layout,
        non_exhaustive: (),
    },
}

enum AllocInit {
    /// The contents of the new memory are uninitialized.
    Uninitialized,
    /// The new memory is guaranteed to be zeroed.
    Zeroed,
}

#[predicate]
fn all_none<T>(l: Seq<Option<T>>) {
    assertion!((l == Seq::empty()));
    assertion!(|rest| all_none(rest) * (l == rest.prepend(None)));
}

#[lemma]
#[requires(ptr.many_uninits(cap))]
#[ensures(|l| raw_vec_left(ptr, cap, l) * all_none(l))]
fn uninit_to_raw_vec<T: Ownable>(ptr: *mut T, cap: usize);

impl Ownable for AllocInit {
    type RepresentationTy = Self;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!((self == model))
    }
}

#[predicate]
fn raw_vec_left<T: Ownable>(
    ptr: In<*mut T>,
    cap: In<usize>,
    content: Seq<Option<T::RepresentationTy>>,
) {
    assertion!((cap == 0) * (content == Seq::empty()));
    assertion!(|v, v_repr, rest| (cap > 0) * (ptr -> v) * v.own(v_repr) * raw_vec_left(ptr.offset(1), cap - 1, rest) * (content == rest.prepend(Some(v_repr))) * (cap == content.len()));
    assertion!(|rest| (cap > 0)
        * ptr.uninit()
        * raw_vec_left(ptr.offset(1), cap - 1, rest)
        * (cap == content.len())
        * (content == rest.prepend(None)));
}

// Modified to remove alloctaor
pub(crate) struct RawVec<T> {
    ptr: Unique<T>,
    cap: usize,
}

pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

impl<T: Ownable> Ownable for RawVec<T> {
    type RepresentationTy = Seq<Option<T::RepresentationTy>>;

    #[predicate]
    fn own(self, content: Self::RepresentationTy) {
        assertion!(raw_vec_left(self.ptr.as_ptr(), self.cap, content))
    }
}

impl<T: Ownable> RawVec<T> {
    #[ensures(ret.own(Seq::empty()))]
    pub fn new() -> Self {
        Self {
            ptr: Unique::dangling(),
            cap: 0,
        }
    }

    #[requires(init.own(AllocInit::Uninitialized) * capacity.own(capacity) * (capacity < (2 << 62)))]
    #[ensures(|x| ret.own(x))]
    fn allocate_in(capacity: usize, init: AllocInit) -> Self {
        // Don't allocate here because `Drop` will not deallocate when `capacity` is 0.
        if T::IS_ZST || capacity == 0 {
            Self::new()
        } else {
            let layout = match Layout::array::<T>(capacity) {
                Ok(layout) => layout,
                Err(_) => capacity_overflow(),
            };
            match alloc_guard(layout.size()) {
                Ok(_) => {}
                Err(_) => capacity_overflow(),
            }
            let result = match init {
                AllocInit::Uninitialized => GillianAllocator.allocate(layout),
                AllocInit::Zeroed => GillianAllocator.allocate_zeroed(layout),
            };
            let ptr = match result {
                Ok(ptr) => ptr,
                Err(_) => handle_alloc_error(layout),
            };
            let ptr = unsafe { Unique::new_unchecked(ptr.cast().as_ptr()) };
            uninit_to_raw_vec(ptr.as_ptr(), capacity);
            Self { ptr, cap: capacity }
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self::allocate_in(capacity, AllocInit::Uninitialized)
    }
}

fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

fn handle_alloc_error(_layout: Layout) -> ! {
    panic!("allocation failed!")
}

// We need to guarantee the following:
// * We don't ever allocate `> isize::MAX` byte-size objects.
// * We don't overflow `usize::MAX` and actually allocate too little.
//
// On 64-bit we just need to check for overflow since trying to allocate
// `> isize::MAX` bytes will surely fail. On 32-bit and 16-bit we need to add
// an extra guard for this in case we're running on a platform which can use
// all 4GB in user-space, e.g., PAE or x32.

#[inline]
fn alloc_guard(alloc_size: usize) -> Result<(), TryReserveError> {
    if usize::BITS < 64 && alloc_size > isize::MAX as usize {
        Err(TryReserveErrorKind::CapacityOverflow.into())
    } else {
        Ok(())
    }
}

#![feature(ptr_internals)]
#![feature(sized_type_properties)]
#![feature(allocator_api)]
#![feature(unchecked_math)]
extern crate gilogic;

use gilogic::{
    __stubs::PointsToMaybeUninit,
    alloc::GillianAllocator,
    macros::{assertion, ensures, lemma, predicate, requires},
    // mutref_auto_resolve,
    prophecies::Ownable,
    Seq,
};
use std::alloc::{Allocator, Layout, LayoutError};
use std::mem::{self, SizedTypeProperties};
use std::ptr::{NonNull, Unique};

pub struct TryReserveError {
    kind: TryReserveErrorKind,
}

impl From<TryReserveErrorKind> for TryReserveError {
    fn from(kind: TryReserveErrorKind) -> Self {
        Self { kind }
    }
}

impl TryReserveError {
    fn kind(&self) -> TryReserveErrorKind {
        self.kind
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

use TryReserveErrorKind::*;

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

fn handle_reserve(result: Result<(), TryReserveError>) {
    match result {
        Err(err) => match err.kind() {
            CapacityOverflow => capacity_overflow(),
            AllocError { layout, .. } => handle_alloc_error(layout),
        },
        Ok(()) => { /* yay */ }
    }
}

#[predicate]
fn raw_vec_left<T: Ownable>(
    ptr: In<*mut T>,
    cap: In<usize>,
    content: Seq<Option<T::RepresentationTy>>,
) {
    assertion!((cap == 0) * (content == Seq::empty()));
    assertion!(|v, v_repr, rest|
            (cap > 0) * (ptr -> v) * v.own(v_repr) * raw_vec_left(ptr.offset(1), cap - 1, rest) * (content == rest.prepend(Some(v_repr))) * (cap == content.len()));
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
        assertion!(
            |ptr, cap| (self == RawVec { ptr, cap }) * raw_vec_left(ptr.as_ptr(), cap, content)
        )
    }
}

fn finish_grow(
    new_layout: Result<Layout, LayoutError>,
    current_memory: Option<(NonNull<u8>, Layout)>,
) -> Result<NonNull<[u8]>, TryReserveError> {
    // Check for the error here to minimize the size of `RawVec::grow_*`.
    let new_layout = match new_layout {
        Ok(x) => x,
        Err(_) => {
            return Err(TryReserveError {
                kind: CapacityOverflow,
            })
        }
    };

    match alloc_guard(new_layout.size()) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };

    let memory = if let Some((ptr, old_layout)) = current_memory {
        // debug_assert_eq!(old_layout.align(), new_layout.align());
        unsafe {
            // The allocator checks for alignment equality
            assert!(old_layout.align() == new_layout.align());
            GillianAllocator.grow(ptr, old_layout, new_layout)
        }
    } else {
        GillianAllocator.allocate(new_layout)
    };

    match memory {
        Ok(x) => Ok(x),
        Err(_) => Err(AllocError {
            layout: new_layout,
            non_exhaustive: (),
        }
        .into()),
    }
}

impl<T: Ownable> RawVec<T> {
    const MIN_NON_ZERO_CAP: usize = if mem::size_of::<T>() == 1 {
        8
    } else if mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    };

    #[ensures(ret.own(Seq::empty()))]
    pub fn new() -> Self {
        Self {
            ptr: Unique::dangling(),
            cap: 0,
        }
    }

    fn current_memory(&self) -> Option<(NonNull<u8>, Layout)> {
        if T::IS_ZST || self.cap == 0 {
            None
        } else {
            unsafe {
                let align = 1; // We don't support align yet, but plan on supporting them exactly in the same way we support size_of.
                               // It's just more implementation and lack of type, but the skeleton is already there in LayoutKnowlege.
                let size = mem::size_of::<T>().unchecked_mul(self.cap);
                let layout = Layout::from_size_align_unchecked(size, align);
                Some((self.ptr.cast().into(), layout))
            }
        }
    }

    #[requires(init.own(AllocInit::Uninitialized) * capacity.own(capacity) * (capacity < 2 << 62))]
    #[ensures(|x| ret.own(x) * all_none(x))]
    fn allocate(capacity: usize, init: AllocInit) -> Self {
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

    #[requires(|current: <Self as Ownable>::RepresentationTy, future: <Self as Ownable>::RepresentationTy| self.own((current, future)) * len.own(len) * additional.own(additional) * (additional > 0))]
    #[ensures(emp)]
    fn grow_amortized(&mut self, len: usize, additional: usize) -> Result<(), TryReserveError> {
        // This is ensured by the calling contexts.
        // assert!(additional > 0);

        if T::IS_ZST {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(TryReserveError {
                kind: CapacityOverflow,
            });
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = match len.checked_add(additional) {
            Some(x) => x,
            None => {
                return Err(TryReserveError {
                    kind: CapacityOverflow,
                })
            }
        };

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = std::cmp::max(self.cap * 2, required_cap);
        let cap = std::cmp::max(Self::MIN_NON_ZERO_CAP, cap);

        let new_layout = Layout::array::<T>(cap);

        // `finish_grow` is non-generic over `T`.
        let ptr = match finish_grow(new_layout, self.current_memory()) {
            Ok(ptr) => ptr,
            Err(err) => return Err(err),
        };
        self.ptr = unsafe { Unique::new_unchecked(ptr.cast().as_ptr()) };
        self.cap = cap;
        Ok(())
    }

    #[requires(capacity.own(capacity) * (capacity < 2 << 62))]
    #[ensures(|model| ret.own(model) * all_none(model))]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::allocate(capacity, AllocInit::Uninitialized)
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

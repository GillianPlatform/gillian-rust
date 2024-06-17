//@check-pass
#![feature(ptr_internals)]
#![feature(sized_type_properties)]
#![feature(allocator_api)]
#![feature(unchecked_math)]
extern crate gilogic;

use gilogic::{
    __stubs::{PointsToMaybeUninit, PointsToSlice},
    alloc::GillianAllocator,
    macros::{assertion, lemma, predicate, specification},
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised},
    Seq,
};
use std::alloc::{Allocator, Layout, LayoutError};
use std::mem::{self, SizedTypeProperties};
use std::ptr::{NonNull, Unique};

macro_rules! branch {
    ($cond:expr) => {
        if $cond {
        } else {
        }
    };
}

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

#[derive(Clone, Copy)]
pub enum TryReserveErrorKind {
    /// Error due to the comxputed capacity exceeding the collection's maximum
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
pub fn all_own<T: Ownable>(vs: In<Seq<T>>, reprs: Seq<T::RepresentationTy>) {
    assertion!((vs == Seq::empty()) * (reprs == Seq::empty()));
    assertion!(|x: T,
                x_repr: T::RepresentationTy,
                rest: Seq<T>,
                rest_repr: Seq<T::RepresentationTy>| (vs == rest.append(x))
        * x.own(x_repr)
        * all_own(rest, rest_repr)
        * (reprs == rest_repr.append(x_repr)))
}

// #[lemma]
// #[requires(|content: Seq<Option<T>>, repr: Seq<Option<T::RepresentationTy>>|
//             (before < after) * ptr.many_maybe_uninit(before, content) * all_own(content, repr) *
//             ptr.add(before).many_uninits(after - before))]
// #[ensures(|nones: Seq<Option<T>>, nones_r: Seq<Option<T::RepresentationTy>>|
//             ptr.many_maybe_uninit(after, content.concat(nones)) * all_own(content.concat(nones), repr.concat(nones_r)) *
//             (nones.len() == after - before) * (nones.len() == nones_r.len()) *
//             all_none(nones) * all_none(nones_r))]
// fn concat_own_uninit<T: Ownable>(ptr: *mut T, before: usize, after: usize);

// #[lemma]
// #[requires(ptr.many_uninits(cap))]
// #[ensures(
//         ptr.many_maybe_uninit(cap, Seq::<Option<T>>::repeat(None, cap)) *
//         all_own(Seq::<Option<T>>::repeat(None, cap), Seq::<Option<T::RepresentationTy>>::repeat(None, cap))
//     )]
// fn uninit_to_raw_vec<T: Ownable>(ptr: *mut T, cap: usize);

// Modified to remove alloctaor
pub(crate) struct RawVec<T> {
    ptr: Unique<T>,
    cap: usize,
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

impl<T> RawVec<T> {
    const MIN_NON_ZERO_CAP: usize = if mem::size_of::<T>() == 1 {
        8
    } else if mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    };

    pub const fn new() -> Self {
        Self {
            ptr: Unique::dangling(),
            cap: 0,
        }
    }

    pub const NEW: Self = Self::new();

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

    // #[requires(init.own(AllocInit::Uninitialized) * capacity.own(capacity) * (capacity < 2 << 62))]
    // #[ensures(ret.own(Seq::repeat(None, capacity)))]
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
            Self { ptr, cap: capacity }
        }
    }

    pub fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    // #[requires(|current: <Self as Ownable>::RepresentationTy, future: <Self as Ownable>::RepresentationTy| self.own((current, future)) * len.own(len) * additional.own(additional) * (additional > 0))]
    // #[ensures(
    //         $future.len() - current.len() >= additional$ // Note quite that
    //         $future == current.concat(Seq::repeat(future.len() - current.len()))$
    //  )]
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

    pub fn capacity(&self) -> usize {
        if T::IS_ZST {
            usize::MAX
        } else {
            self.cap
        }
    }

    pub fn reserve_for_push(&mut self, len: usize) {
        handle_reserve(self.grow_amortized(len, 1));
    }

    // #[requires(capacity.own(capacity) * (capacity < 2 << 62))]
    // #[ensures(|model| ret.own(model) * (model == Seq::repeat(None, model.len())))]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::allocate(capacity, AllocInit::Uninitialized)
    }
}

fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

#[allow(unused_variables)]
fn handle_alloc_error(layout: Layout) -> ! {
    panic!("allocation failed!")
}

fn alloc_guard(alloc_size: usize) -> Result<(), TryReserveError> {
    if usize::BITS < 64 && alloc_size > isize::MAX as usize {
        Err(TryReserveErrorKind::CapacityOverflow.into())
    } else {
        Ok(())
    }
}

pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

impl<T: Ownable> Ownable for Vec<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(
            |values: Seq<T>, ptr, cap, len| (std::mem::size_of::<T>() == 0)
                * (self
                    == Vec {
                        buf: RawVec { ptr, cap },
                        len
                    })
                * cap.own(cap)
                * len.own(len)
                * (cap == 0)
                * ptr.as_ptr().points_to_slice(len, values)
                * all_own(values, model)
                * (values.len() == model.len())
        );
        assertion!(|ptr, cap, len, values, rest| (std::mem::size_of::<T>() > 0)
            * (self
                == Vec {
                    buf: RawVec { ptr, cap },
                    len
                })
            * cap.own(cap)
            * len.own(len)
            * (len <= cap)
            * ptr.as_ptr().points_to_slice(len, values)
            * (values.len() == model.len())
            * all_own(values, model)
            * ptr.as_ptr().add(len).many_maybe_uninits(cap - len, rest))
    }
}

impl<T: Ownable> Vec<T> {
    #[specification(
        requires { emp }
        ensures { ret.own(Seq::empty())}
    )]
    pub const fn new() -> Self {
        branch!(T::IS_ZST);
        Vec {
            buf: RawVec::NEW,
            len: 0,
        }
    }

    #[specification(
        requires { capacity.own(capacity) * (capacity < 2 << 62 )}
        ensures { ret.own(Seq::empty()) }
    )]
    pub fn with_capacity(capacity: usize) -> Self {
        Vec {
            buf: RawVec::with_capacity(capacity),
            len: 0,
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.ptr()
    }

    // #[requires(|
    //     current: <Self as Ownable>::RepresentationTy,
    //     future: <Self as Ownable>::RepresentationTy,
    //     v_repr: <T as Ownable>::RepresentationTy|
    //     self.own((current, future)) *
    //     (current.len() < 2 << 62) *
    //     value.own(v_repr))]
    // #[ensures($future == current.prepend(v_repr)$)]
    pub fn push(&mut self, value: T) {
        // This will panic or abort if we would allocate > isize::MAX bytes
        // or if the length increment would overflow for zero-sized types.
        if self.len == self.buf.capacity() {
            self.buf.reserve_for_push(self.len);
        }
        unsafe {
            let end = self.as_mut_ptr().add(self.len);
            std::ptr::write(end, value);
            self.len += 1;
            mutref_auto_resolve!(self);
        }
    }
}

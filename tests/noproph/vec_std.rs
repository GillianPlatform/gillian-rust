//@check-pass
#![feature(ptr_internals)]
#![feature(sized_type_properties)]
#![feature(allocator_api)]
#![feature(unchecked_math)]
extern crate gilogic;

use gilogic::{
    __stubs::{PointsToMaybeUninit, PointsToSlice},
    alloc::GillianAllocator,
    iterated::no_prophecies::{all_own, all_own_swap},
    macros::*,
    Ownable,
};
use std::alloc::{Allocator, Layout, LayoutError};
use std::mem::{self, SizedTypeProperties};
use std::ptr::{NonNull, Unique};
use std::slice;

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
    #[predicate]
    fn own(self) {
        assertion!((1 == 1))
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
    // Capacity overflow!
    panic!();
}

#[allow(unused_variables)]
fn handle_alloc_error(layout: Layout) -> ! {
    // Allocation failed!
    panic!()
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

// We don't currently have a way to use proof tactics within the body of a function
// Because of MIR vs THIR compilation... The engineering behind this is a nightmare.
// So we use a lemma that asserts the right thing to do the work.
#[lemma]
#[specification(
    forall values.
    requires { p.points_to_slice(len, values) * all_own(values) }
    ensures { p.points_to_slice(len, values) * all_own(values) }
)]
fn assert_correct_vs<T: Ownable>(p: *const T, len: usize);

#[extract_lemma(
    forall ptr: Unique<T>, cap, len.
    assuming { ix < len }
    from { vec_ref_mut_pcl(vec, (ptr, cap, len)) }
    extract { Ownable::own(&mut (*(ptr.as_ptr().add(ix)))) }
)]
#[gillian::trusted]
fn extract_ith<'a, T: Ownable>(vec: &'a mut Vec<T>, ix: usize);

#[with_freeze_lemma(
    lemma_name = freeze_pcl,
    predicate_name = vec_ref_mut_pcl,
    frozen_variables = [ptr, cap, len],
)]
impl<T: Ownable> Ownable for Vec<T> {
    #[predicate]
    fn own(self) {
        // The specification for zsts is quite hard. We need a value like ZST::REPRESENTATIVE or something.
        // assertion!(
        //     |values: Seq<T>, ptr, cap, len| (std::mem::size_of::<T>() == 0)
        //         * (self
        //             == Vec {
        //                 buf: RawVec { ptr, cap },
        //                 len
        //             })
        //         * cap.own(cap)
        //         * len.own(len)
        //         * (cap == 0)
        //         * ptr.as_ptr().points_to_slice(len, values)
        //         * all_own(values, model)
        //         * (values.len() == model.len())
        // );
        assertion!(
            |ptr: Unique<T>, cap: usize, len: usize, values, rest| (std::mem::size_of::<T>() > 0)
                * (self
                    == Vec {
                        buf: RawVec { ptr, cap },
                        len
                    })
                * cap.own()
                * len.own()
                * (len <= cap)
                * ptr.as_ptr().points_to_slice(len, values)
                * (len == values.len())
                * all_own(values)
                * ptr.as_ptr().add(len).many_maybe_uninits(cap - len, rest)
        )
    }
}

impl<T: Ownable> Vec<T> {
    #[show_safety]
    pub const fn new() -> Self {
        branch!(T::IS_ZST);
        Vec {
            buf: RawVec::NEW,
            len: 0,
        }
    }

    #[show_safety]
    pub fn with_capacity(capacity: usize) -> Self {
        Vec {
            buf: RawVec::with_capacity(capacity),
            len: 0,
        }
    }

    pub fn as_ptr(&self) -> *const T {
        // We shadow the slice method of the same name to avoid going through
        // `deref`, which creates an intermediate reference.
        self.buf.ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.ptr()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    #[show_safety]
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
        }
    }

    pub fn swap(&mut self, a: usize, b: usize) {
        // Some ghost code to keep track of the model.
        freeze_pcl(self);

        // FIXME: use swap_unchecked here (https://github.com/rust-lang/rust/pull/88540#issuecomment-944344343)
        // Can't take two mutable loans from one vector, so instead use raw pointers.
        let slice = unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) };

        let pa = std::ptr::addr_of_mut!(slice[a]);
        let pb = std::ptr::addr_of_mut!(slice[b]);
        // SAFETY: `pa` and `pb` have been created from safe mutable references and refer
        // to elements in the slice and therefore are guaranteed to be valid and aligned.
        // Note that accessing the elements behind `a` and `b` is checked and will
        // panic when out of bounds.
        unsafe {
            std::ptr::swap(pa, pb);
        }
        // We need assert_bind to be able to talk about `curr`
        // all_own_swap(curr, a, b);
    }

    #[show_safety]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                // This is core::hint::assert_unchecked in the real implementation
                assert!(self.len < self.capacity());
                if self.len == 0 {}; // This is because of a very annoying normalisation issue in Gillian...
                assert_correct_vs(self.as_ptr(), self.len);
                Some(std::ptr::read(self.as_ptr().add(self.len)))
            }
        }
    }

    #[show_safety]
    pub fn index_mut(&mut self, ix: usize) -> &mut T {
        freeze_pcl(self);
        // from impl<T> ops::DerefMut for Vec<T>
        let slice = unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) };

        // from SliceIndex<[T]> for usize, which is directly called by IndexMut<usize> for [T],
        // which in turn is called by IndexMut<usize> for Vec<T>
        let ret = &mut slice[ix];

        extract_ith(self, ix);
        ret
    }

    #[show_safety]
    pub unsafe fn get_unchecked_mut(&mut self, ix: usize) -> &mut T {
        freeze_pcl(self);
        // from impl<T> ops::DerefMut for Vec<T>
        let slice = unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) };

        //safety assert!
        assert!(ix < self.len);

        // from SliceIndex<[T]> for usize, which is directly called by IndexMut<usize> for [T],
        // which in turn is called by IndexMut<usize> for Vec<T>
        let ret = &mut *slice.as_mut_ptr().add(ix);
        extract_ith(self, ix);
        ret
    }

    #[show_safety]
    fn get_mut(&mut self, ix: usize) -> Option<&mut T> {
        // SAFETY: `self` is checked to be in bounds.
        if ix < self.len {
            // Ignore specification to avoid having to manually reborrow
            unsafe { Some(self.get_unchecked_mut(ix)) }
        } else {
            None
        }
    }
}

// We can't compile this at the moment because of poor_mans_unification...
// unsafe trait MySliceIndexMut<T>
// where
//     T: ?Sized,
// {
//     type Output: ?Sized;
//     fn get_unchecked_mut(self, slice: &mut T) -> *mut Self::Output;
//     fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
//     fn index_mut(self, slice: &mut T) -> &mut Self::Output;
// }

// unsafe impl<T> MySliceIndexMut<[T]> for usize {
//     type Output = T;

//     fn index_mut(self, slice: &mut [T]) -> &mut T {
//         &mut (*slice)[self]
//     }

//     fn get_unchecked_mut(self, slice: &mut [T]) -> *mut T {
//         // SAFETY: see comments for `get_unchecked` above.
//         unsafe { slice.as_mut_ptr().add(self) }
//     }

//     fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
//         // SAFETY: `self` is checked to be in bounds.
//         if self < slice.len() {
//             unsafe { Some(&mut *self.get_unchecked_mut(slice)) }
//         } else {
//             None
//         }
//     }
// }

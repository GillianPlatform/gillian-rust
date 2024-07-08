//@check-pass
//?gil:ignore
#![feature(ptr_internals)]
#![feature(sized_type_properties)]
#![feature(allocator_api)]
#![feature(unchecked_math)]
extern crate gilogic;

use gilogic::{
    __stubs::{PointsToMaybeUninit, PointsToSlice},
    alloc::GillianAllocator,
    iterated::{all_own, all_own_swap},
    macros::{
        assertion, extract_lemma, predicate, prophecies::with_freeze_lemma_for_mutref,
        specification,
    },
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised, Prophecy},
    Seq,
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

pub struct VecDeque<T> {
    buf: RawVec<T>,
    len: usize,
    head: usize,
}

// #[extract_lemma(
//     forall ptr: Unique<T>, cap, len.
//     model m.
//     extract model mh: (T::RepresentationTy, T::RepresentationTy).
//     assuming { ix < len }
//     from { vec_ref_mut_pcl(vec, m, ptr, cap, len) }
//     extract { Ownable::own(&mut (*(ptr.as_ptr().add(ix))), mh) }
//     prophecise { m.sub(0, ix).append(mh).concat(m.sub(ix + 1, len - ix - 1)) }
// )]
// fn extract_ith<'a, T: Ownable>(vec: &'a mut Vec<T>, ix: usize) -> Prophecy<T::RepresentationTy>;

// #[with_freeze_lemma_for_mutref(
//     lemma_name = freeze_pcl,
//     predicate_name = vec_ref_mut_pcl,
//     frozen_variables = [ptr, cap, len],
//     inner_predicate_name = vec_ref_mut_inner_pcl,
//     resolve_macro_name = auto_resolve_vec_ref_mut_pcl
// )]
impl<T: Ownable> Ownable for VecDeque<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(
            |ptr: Unique<T>, cap: usize, len: usize, head: usize, values, rest, rest2| (head + len
                <= cap)
                * (std::mem::size_of::<T>() > 0)
                * (self
                    == VecDeque {
                        buf: RawVec { ptr, cap },
                        len,
                        head
                    })
                * cap.own(cap)
                * len.own(len)
                * head.own(head)
                * ptr.as_ptr().add(head).points_to_slice(len, values)
                * (len == values.len())
                * (values.len() == model.len())
                * all_own(values, model)
                * ptr
                    .as_ptr()
                    .add(head + len)
                    .many_maybe_uninits(cap - len, rest)
                * ptr.as_ptr().many_maybe_uninits(head, rest2)
        );
        //                                      head                     cap
        //      +------------------+-------------+------------------------+
        //      | head + len - cap |             |   cap - head           |
        //      +------------------+-------------+------------------------+
        assertion!(|ptr: Unique<T>,
                    cap: usize,
                    len: usize,
                    head: usize,
                    values,
                    values_head: Seq<_>,
                    values_tail,
                    end,
                    rest| (head + len > cap)
            * (head < cap)
            * (len <= cap)
            * (std::mem::size_of::<T>() > 0)
            * (self
                == VecDeque {
                    buf: RawVec { ptr, cap },
                    len,
                    head
                })
            * (end == (head + len - cap))
            * (values == values_head.concat(values_tail))
            * cap.own(cap)
            * len.own(len)
            * head.own(head)
            * ptr
                .as_ptr()
                .add(head)
                .points_to_slice(cap - head, values_head)
            * ptr.as_ptr().points_to_slice(end, values_tail)
            * (len == values.len())
            * (values.len() == model.len())
            * all_own(values, model)
            * ptr.as_ptr().add(end).many_maybe_uninits(cap - len, rest));
    }
}

impl<T: Ownable> VecDeque<T> {
    #[specification(
        requires { emp }
        ensures { ret.own(Seq::empty())}
    )]
    pub const fn new() -> Self {
        branch!(T::IS_ZST);
        VecDeque {
            buf: RawVec::NEW,
            head: 0,
            len: 0,
        }
    }

    #[specification(
        requires { capacity.own(capacity) * (capacity <= isize::MAX as usize)}
        ensures { ret.own(Seq::empty()) }
    )]
    pub fn with_capacity(capacity: usize) -> Self {
        VecDeque {
            buf: RawVec::with_capacity(capacity),
            head: 0,
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    #[creusillian::requires((*self)@.len() < 1000 )]
    #[creusillian::ensures((^self)@ == (*self)@.append(value))]
    pub fn push_back(&mut self, value: T) {
        if self.is_full() {
            self.grow();
        }

        unsafe { self.buffer_write(self.to_physical_idx(self.len()), value) }
        self.len += 1;
        mutref_auto_resolve!(self);
    }

    fn grow(&mut self) {
        // debug_assert!(self.is_full());
        let old_cap = self.capacity();

        self.buf.grow_amortized(self.len, 1);
        unsafe {
            self.handle_capacity_increase(old_cap);
        }

        // debug_assert!(!self.is_full());
    }

    /// Writes an element into the buffer, moving it.
    #[inline]
    unsafe fn buffer_write(&mut self, off: usize, value: T) {
        unsafe {
            // std::ptr::write(self.ptr().add(off), value);
        }
    }

    #[inline]
    fn to_physical_idx(&self, idx: usize) -> usize {
        self.wrap_add(self.head, idx)
    }

    #[inline]
    fn wrap_add(&self, idx: usize, addend: usize) -> usize {
        wrap_index(idx.wrapping_add(addend), self.capacity())
    }

    /// Frobs the head and tail sections around to handle the fact that we
    /// just reallocated. Unsafe because it trusts old_capacity.
    #[inline]
    unsafe fn handle_capacity_increase(&mut self, old_capacity: usize) {
        let new_capacity = self.capacity();
        // debug_assert!(new_capacity >= old_capacity);

        // Move the shortest contiguous section of the ring buffer
        //
        // H := head
        // L := last element (`self.to_physical_idx(self.len - 1)`)
        //
        //    H             L
        //   [o o o o o o o o ]
        //    H             L
        // A [o o o o o o o o . . . . . . . . ]
        //        L H
        //   [o o o o o o o o ]
        //          H             L
        // B [. . . o o o o o o o o . . . . . ]
        //              L H
        //   [o o o o o o o o ]
        //              L                 H
        // C [o o o o o o . . . . . . . . o o ]

        // can't use is_contiguous() because the capacity is already updated.
        if self.head <= old_capacity - self.len {
            // A
            // Nop
        } else {
            let head_len = old_capacity - self.head;
            let tail_len = self.len - head_len;
            if head_len > tail_len && new_capacity - old_capacity >= tail_len {
                // B
                unsafe {
                    self.copy_nonoverlapping(0, old_capacity, tail_len);
                }
            } else {
                // C
                let new_head = new_capacity - head_len;
                unsafe {
                    // can't use copy_nonoverlapping here, because if e.g. head_len = 2
                    // and new_capacity = old_capacity + 1, then the heads overlap.
                    self.copy(self.head, new_head, head_len);
                }
                self.head = new_head;
            }
        }
        // debug_assert!(self.head < self.capacity() || self.capacity() == 0);
    }

    #[inline]
    unsafe fn copy_nonoverlapping(&mut self, src: usize, dst: usize, len: usize) {
        unsafe {
            std::ptr::copy_nonoverlapping(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    unsafe fn copy(&mut self, src: usize, dst: usize, len: usize) {
        unsafe {
            std::ptr::copy(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    #[inline]
    fn ptr(&self) -> *mut T {
        self.buf.ptr()
    }
}

#[inline]
fn wrap_index(logical_index: usize, capacity: usize) -> usize {
    // debug_assert!(
    //     (logical_index == 0 && capacity == 0)
    //         || logical_index < capacity
    //         || (logical_index - capacity) < capacity
    // );
    if logical_index >= capacity {
        logical_index - capacity
    } else {
        logical_index
    }
}

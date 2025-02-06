//@check-pass
extern crate creusillian;
extern crate gilogic;
use gilogic::{
    __stubs::{PointsToMaybeUninit, PointsToSlice},
    alloc::GillianAllocator,
    iterated::with_prophecies::{all_own, all_own_swap},
    macros::*,
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised, Prophecy},
    Seq,
};

/// Vec implementation from https://doc.rust-lang.org/nomicon/vec/vec-final.html
use std::marker::PhantomData;
use std::mem;
use std::ptr;

/// This creates a wrapper around the Rust Alloc API that always fails on allocation failures.
/// The methods will be fully replaced by shims that implement the same functionality in terms of
/// the primitives of our language model.
/// General assumptions we make:
/// - the global allocator has _not_ been reconfigured to not abort on allocation failure,
///   in particular we assume that the allocation failure handler does not panic.
mod rralloc {
    use std::alloc::{self, Layout};

    // RefinedRust does not actually verify this function.
    // Instead it uses the following axiomatised shim in Coq that performs a typed allocation:
    // Definition type_of_alloc_array `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
    //   fn(∀ () : 0 | (size) : (Z), (λ ϝ, []); size @ int usize_t; λ π,
    //     ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ isize_t⌝ ∗
    //     ⌜(size > 0)%Z⌝ ∗
    //     ⌜(size_of_st T_st > 0)%Z⌝) →
    //   ∃ l : loc, l @ alias_ptr_t; λ π,
    //       l ◁ₗ[π, Owned false] .@ (◁ (uninit (ArraySynType T_st (Z.to_nat size)))) ∗
    //       freeable_nz l ((size_of_array_in_bytes T_st (Z.to_nat size))) 1 HeapAlloc

    pub unsafe fn alloc_array<T>(len: usize) -> *mut T {
        gilogic::alloc::alloc_array::<T>(len)
    }

    // RefinedRust does not actually verify this function.
    // Instead it uses the following axiomatised shim in Coq that performs a typed allocation:
    // Definition type_of_realloc_array `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
    //   fn(∀ () : 0 | (old_size, new_size, l, v) : (Z * Z * loc * val), (λ ϝ, []);
    //     old_size @ int usize_t, l @ alias_ptr_t, new_size @ int usize_t; λ π,
    //     freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat old_size)) 1 HeapAlloc ∗
    //     l ◁ₗ[π, Owned false] #v @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat old_size)))) ∗
    //     ⌜(old_size ≤ new_size)%Z⌝ ∗
    //     ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat new_size)) ∈ isize_t⌝ ∗
    //     ⌜(old_size > 0)%Z⌝ ∗
    //     ⌜(size_of_st T_st > 0)%Z⌝) →
    //   ∃ (l', v') : (loc * val), l' @ alias_ptr_t; λ π,
    //     l' ◁ₗ[π, Owned false] #(v ++ v') @ (◁ (value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat new_size))))) ∗
    //     v' ◁ᵥ{π} .@ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat (new_size - old_size)))) ∗
    //   freeable_nz l' ((size_of_array_in_bytes T_st (Z.to_nat new_size))) 1 HeapAlloc.

    // We just write a similar function in Rust
    pub unsafe fn realloc_array<T>(old_len: usize, ptr: *mut T, new_len: usize) -> *mut T {
        let new_ptr = gilogic::alloc::alloc_array::<T>(new_len);
        std::ptr::copy_nonoverlapping(ptr, new_ptr, old_len);
        gilogic::alloc::dealloc_array(ptr, old_len);
        new_ptr
    }

    pub unsafe fn dealloc_array<T>(len: usize, ptr: *mut T) {
        alloc::dealloc(ptr as *mut u8, Layout::array::<T>(len).unwrap());
    }
}

/// A wrapper module around ptr operations we need.
mod rrptr {
    use std::ptr::NonNull;

    pub fn dangling<T>() -> *mut T {
        NonNull::dangling().as_ptr()
    }

    // We only need these shims because we cannot get their DefIds in the frontend currently..
    pub unsafe fn mut_offset<T>(ptr: *mut T, count: isize) -> *mut T {
        ptr.offset(count)
    }

    pub unsafe fn const_offset<T>(ptr: *const T, count: isize) -> *const T {
        ptr.offset(count)
    }
    pub unsafe fn mut_add<T>(ptr: *mut T, count: usize) -> *mut T {
        ptr.add(count)
    }

    pub unsafe fn const_add<T>(ptr: *const T, count: usize) -> *const T {
        ptr.add(count)
    }
}

/// Represents an owned chunk of memory of which a prefix `xs` is filled with elements of type `T`,
/// with a total capacity to hold `cap` elements of `T`.
// Compared to the Rustonomicon implementation, we use *const T instead of NonNull<T>.
// The only difference is that the null bitpattern can't be used for niche optimizations in our case.
// only part of the invariant for the ownership predicate, not sharing
pub struct RawVec<T> {
    // *const T because it is covariant in T
    ptr: *const T,
    cap: usize,
    _marker: PhantomData<T>,
}

// #[with_freeze_lemma_for_mutref(
//     lemma_name = freeze_pcl,
//     predicate_name = vec_ref_mut_pcl,
//     frozen_variables = [ptr, cap, len],
//     inner_predicate_name = vec_ref_mut_inner_pcl,
//     resolve_macro_name = auto_resolve_vec_ref_mut_pcl
// )]
impl<T: Ownable> Ownable for Vec<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(
            |ptr: *const T, cap: usize, len: usize, values, rest| (std::mem::size_of::<T>() > 0)
                * (self
                    == Vec {
                        buf: RawVec {
                            ptr,
                            cap,
                            _marker: PhantomData
                        },
                        len
                    })
                * cap.own(cap)
                * len.own(len)
                * (len <= cap)
                * ptr.points_to_slice(len, values)
                * (len == values.len())
                * (values.len() == model.len())
                * all_own(values, model)
                * ptr.add(len).many_maybe_uninits(cap - len, rest)
        )
    }
}

// #[extract_lemma(
//     forall ptr, cap, len.
//     model m.
//     extract model mh.
//     assuming { ix < len }
//     from { vec_ref_mut_pcl(vec, m, ptr, cap, len) }
//     extract { Ownable::own(&mut (*(ptr.add(ix))), mh) }
//     prophecise { m.sub(0, ix).append(mh).concat(m.sub(ix + 1, len - ix - 1)) }
// )]
// fn extract_ith<'a, T: Ownable>(vec: &'a mut Vec<T>, ix: usize) -> Prophecy<T::RepresentationTy>;

pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

impl<T> RawVec<T> {
    pub fn ptr(&self) -> *mut T {
        self.ptr as *mut T
    }

    pub fn cap(&self) -> usize {
        self.cap
    }

    pub fn new() -> Self {
        // !0 is usize::MAX. This branch should be stripped at compile time.
        let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };

        // `NonNull::dangling()` doubles as "unallocated" and "zero-sized allocation"
        RawVec {
            ptr: rrptr::dangling(),
            cap,
            _marker: PhantomData,
        }
    }

    pub fn grow(&mut self) {
        // unfold invariant - it will be broken quite consistently throughout
        // also need to learn the pure facts to pass all the checks.

        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        // capacity overflow?
        assert!(mem::size_of::<T>() != 0);
        // from here on: can assume we don't have a ZST

        let new_cap = if self.cap == 0 {
            // in this case, layouting of the array should never fail
            // we need the fact that size_of T ≤ isize::MAX for that.
            1
        } else {
            // This can't overflow because we ensure self.cap <= isize::MAX,
            // unless the type is a ZST
            let new_cap = 2 * self.cap;
            new_cap
        };

        // Ensure that the new allocation doesn't exceed `isize::MAX` bytes.
        // This limit is due to GEP / ptr::offset taking isize offsets, so Rust std generally
        // limits allocations to isize::MAX bytes.
        // Allocation too large?

        let new_ptr = if self.cap == 0 {
            unsafe { rralloc::alloc_array::<T>(new_cap) }
        } else {
            // this works because we have already checked that the new array is layoutable
            let old_ptr = self.ptr;
            unsafe { rralloc::realloc_array::<T>(self.cap, old_ptr as *mut T, new_cap) }
        };

        // move ownership into self.ptr
        self.ptr = new_ptr as *const T;
        self.cap = new_cap;

        // fold invariant
    }
}

impl<T: Ownable> Vec<T> {
    fn ptr<'a>(&'a self) -> *mut T {
        self.buf.ptr() as *mut T
    }

    fn cap<'a>(&'a self) -> usize {
        self.buf.cap
    }

    pub fn len(&self) -> usize {
        self.len
    }

    #[creusillian::ensures(ret@ == Seq::empty())]
    pub fn new() -> Self {
        Vec {
            buf: RawVec::new(),
            len: 0,
        }
    }

    // TODO: implement support for size_of in Creusillian
    #[specification(
        forall current, future, v_repr.
        requires {
            self.own((current, future)) *
            $(current.len() * 2 * mem::size_of::<T>()) < (isize::MAX as usize)$ *
            elem.own(v_repr)
        }
        ensures {
            $future == current.append(v_repr)$
        }
    )]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap() {
            self.buf.grow();
        }

        // important: ptr::write does not call drop on the uninit mem.
        unsafe {
            ptr::write(rrptr::mut_add(self.ptr(), self.len), elem);
        }

        // Can't overflow, we'll OOM first.
        self.len += 1;
        assert!(self.cap() <= usize::MAX); // For the prover
        mutref_auto_resolve!(self);
    }

    #[creusillian::ensures(match ret {
        None => ((*self@) == Seq::empty()) && ((^self@) == Seq::empty()),
        Some(last) => ((^self@) == (*self@).sub(0, (*self@).len() - 1)) && ((*self@).last() == last@)
     })]
    pub fn pop(&mut self) -> Option<T> {
        let res = if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(ptr::read(rrptr::mut_add(self.ptr(), self.len))) }
        };
        mutref_auto_resolve!(self);
        res
    }

    // #[creusillian::requires(index < (*self@).len())]
    // #[creusillian::ensures((*self@).at(index) == (*ret@) && (^self@) == (*self@).sub(0, index).append((^ret@)).concat((*self@).sub(index + 1, (*self@).len() - index - 1)))]
    // pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
    //     freeze_pcl(self);
    //     assert!(index < self.len);
    //     unsafe {
    //         let p = rrptr::mut_add(self.ptr(), index);
    //         let ret = &mut *p;
    //         let proph = extract_ith(self, index);
    //         ret.with_prophecy(proph)
    //     }
    // }

    // #[creusillian::ensures(match ret@ {
    //     None => (((*self@).len() <= index) && ((*self@) == (^self@))),
    //     Some(r) =>
    //         ((*self@).at(index) == (*r@)) &&
    //         ((^self@).at(index) == (^r@)) &&
    //         ((^self@) == (*self@).sub(0, index).append((^r@)).concat((*self@).sub(index + 1, (*self@).len() - index - 1)))
    // })]
    // pub fn get_mut<'a>(&'a mut self, index: usize) -> Option<&'a mut T> {
    //     if index < self.len() {
    //         unsafe { Some(self.get_unchecked_mut(index)) }
    //     } else {
    //         mutref_auto_resolve!(self);
    //         None
    //     }
    // }
}

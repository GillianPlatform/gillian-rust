// COPIED FROM: 
// License from RefiedRust applies
// https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/blob/f8f5c8ec71239a4ce7453588101f2bfa79004135/case_studies/minivec/src/lib.rs

#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::import("refinedrust.extra_proofs.minivec", "minivec")]
#![rr::include("option")]
#![allow(dead_code)]

/// Vec implementation from https://doc.rust-lang.org/nomicon/vec/vec-final.html

use std::marker::PhantomData;
use std::mem;
use std::ptr;

mod client;


/// This creates a wrapper around the Rust Alloc API that always fails on allocation failures.
/// The methods will be fully replaced by shims that implement the same functionality in terms of
/// the primitives of our language model.
/// General assumptions we make:
/// - the global allocator has _not_ been reconfigured to not abort on allocation failure,
///   in particular we assume that the allocation failure handler does not panic.
mod rralloc {
    use std::alloc::{self, Layout};

    #[rr::shim("alloc_array", "type_of_alloc_array")]
    pub unsafe fn alloc_array<T>(len: usize) -> *mut T {
        assert!(len > 0);
        // checks that size is ≤ MaxInt isize
        let ly = Layout::array::<T>(len).unwrap();

        // will return null on alloc failure due to
        // - memory exhaustion (but abortion is also allowed behavior in this case)
        // - `ly` not meeting the allocator's size or alignment constraints
        let ptr = alloc::alloc(ly);
        if ptr.is_null() {
            // due to our assumption, this will abort.
            alloc::handle_alloc_error(ly);
        }
        ptr as *mut T
    }

    // For preconditions, see the preconditions of the shim.
    #[rr::shim("realloc_array", "type_of_realloc_array")]
    pub unsafe fn realloc_array<T>(old_len: usize, ptr: *mut T, new_len: usize) -> *mut T {
        assert!(new_len > 0);
        // fine: checks that size is ≤ MaxInt isize
        let old_layout = Layout::array::<T>(old_len).unwrap();
        // fine: same reason
        let new_layout = Layout::array::<T>(new_len).unwrap();

        // will return null on realloc failure -- in this case, the original ptr stays intact
        //    => We directly abort here to match the semantics of our shim
        // - new_len is rounded up to nearest multiple of alignment, and this value must be < usize_max (yes, strictly!)
        //   => trivially satisfied since we have an array layout
        // - the layout with which it was allocated is the same as old_layout
        //   => ensured by the freeable precondition
        // - we rely here on the fact that old_layout and new_layout will have the same alignment
        //   => trivial due to how we construct the layouts
        // - internally, these functions rely on the fact that rustc guarantees that type alignment is a power of 2
        //   => we also have that guarantee by design
        // - the array layout seems to rely on the fact that size is divisible by alignment, as it
        //   does not account for any padding to handle alignment
        //   => we also handle it that way for now

        let ptr = alloc::realloc(ptr as *mut u8, old_layout, new_layout.size());
        if ptr.is_null() {
            // due to our assumption, this will abort.
            alloc::handle_alloc_error(new_layout);
        }
        ptr as *mut T
    }

    #[rr::shim("free_array", "type_of_free_array")]
    pub unsafe fn dealloc_array<T>(len: usize, ptr: *mut T) {
        alloc::dealloc(ptr as *mut u8, Layout::array::<T>(len).unwrap());
    }

    /// Check that an array of `T` with length `len` is layoutable.
    #[rr::shim("check_array_layoutable", "type_of_check_array_layoutable")]
    pub fn check_array_layoutable<T>(len: usize) -> bool {
        let layout = Layout::array::<T>(len);
        layout.is_ok()
    }
}

/// A wrapper module around ptr operations we need.
mod rrptr {
    use std::ptr::NonNull;


    #[rr::shim("ptr_dangling", "type_of_ptr_dangling")]
    pub fn dangling<T>() -> *mut T{
        NonNull::dangling().as_ptr()
    }

    // We only need these shims because we cannot get their DefIds in the frontend currently..
    #[rr::shim("ptr_offset", "type_of_ptr_offset")]
    pub unsafe fn mut_offset<T>(ptr: *mut T, count: isize) -> *mut T {
        ptr.offset(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_offset")]
    pub unsafe fn const_offset<T>(ptr: *const T, count: isize) -> *const T {
        ptr.offset(count)
    }
    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn mut_add<T>(ptr: *mut T, count: usize) -> *mut T {
        ptr.add(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn const_add<T>(ptr: *const T, count: usize) -> *const T {
        ptr.add(count)
    }
}



























































/// Represents an owned chunk of memory of which a prefix `xs` is filled with elements of type `T`,
/// with a total capacity to hold `cap` elements of `T`.
// Compared to the Rustonomicon implementation, we use *const T instead of NonNull<T>.
// The only difference is that the null bitpattern can't be used for niche optimizations in our case.
#[rr::refined_by("(l, cap)" : "(loc * nat)")]
// only part of the invariant for the ownership predicate, not sharing
#[rr::invariant(#own "freeable_nz l (size_of_array_in_bytes {st_of T} cap) 1 HeapAlloc")]
pub struct RawVec<T> {
    // *const T because it is covariant in T
    #[rr::field("l")]
    ptr: *const T,
    #[rr::field("Z.of_nat cap")]
    cap: usize,
    #[rr::field("tt")]
    _marker: PhantomData<T>,
}

#[rr::refined_by("xs" : "list (place_rfn {rt_of T})")]
#[rr::exists("cap" : "nat", "l" : "loc", "len" : "nat", "els")]
#[rr::invariant(#type "l" : "els" @ "array_t (maybe_uninit {T}) cap")]
#[rr::invariant("Hxs" : "xs = project_vec_els len els")]
#[rr::invariant("Hlook_1": "∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))")]
#[rr::invariant("Hlook_2": "∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)")]
#[rr::invariant("Hlen_eq": "len = length xs")]
#[rr::invariant("Hcap": "len ≤ cap")]
// invariant due to GEP / ptr::offset limits: the total size of the allocation should not exceed isize::max bytes
// we need the ZST case to know that we never call grow except when we have reached the capacity limit
#[rr::invariant("if decide (size_of_st {st_of T} = 0%nat) then cap = Z.to_nat (MaxInt usize_t) else (size_of_array_in_bytes {st_of T} cap ≤ MaxInt isize_t)%Z")]
pub struct Vec<T> {
    #[rr::field("(l, cap)")]
    buf: RawVec<T>,
    #[rr::field("Z.of_nat $ len")]
    len: usize,
}

impl<T> RawVec<T> {
    // needed for VecDeque
    #[rr::params("l", "cap")]
    #[rr::args("#(l, cap)")]
    #[rr::returns("l" @ "alias_ptr_t")]
    pub fn ptr(&self) -> *mut T {
        self.ptr as *mut T
    }

    // needed for VecDeque
    #[rr::params("l", "cap")]
    #[rr::args("#(l, cap)")]
    #[rr::returns("cap")]
    pub fn cap(&self) -> usize {
        self.cap
    }

    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::ensures("cap = if decide (size_of_st {st_of T} = 0%nat) then Z.to_nat (MaxInt usize_t) else 0%nat")]
    #[rr::ensures(#type "l" : "(replicate cap #None)" @ "array_t (maybe_uninit {T}) cap")]
    #[rr::returns("(l, cap)")]
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

    #[rr::params("l", "xs", "cap" : "nat", "γ")]
    #[rr::args("(#(l, cap), γ)")]
    #[rr::requires("Hsz": "(size_of_array_in_bytes {st_of T} (2 * cap) ≤ MaxInt isize_t)%Z")]
    #[rr::requires("Hnot_sz": "(size_of_st {st_of T} > 0)%Z")]
    #[rr::requires(#type "l" : "xs" @ "array_t (maybe_uninit {T}) cap")]
    #[rr::exists("new_cap" : "nat", "l'" : "loc")]
    #[rr::observe("γ": "(l', new_cap)")]
    #[rr::ensures(#type "l'" : "(xs ++ replicate (new_cap - cap) #None)" @ "array_t (maybe_uninit {T}) new_cap")]
    #[rr::ensures("new_cap > cap")]
    #[rr::ensures("(size_of_array_in_bytes {st_of T} new_cap ≤ MaxInt isize_t)%Z")]
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
        assert!(rralloc::check_array_layoutable::<T>(new_cap));

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

impl<T> Vec<T> {

    // private function, take an unfolded type
    // we do not move ownership out, but return an alias to the ptr
    #[rr::params("l" : "loc", "cap" : "nat", "len" : "Z")]
    #[rr::args(#raw "#(-[#(l, cap); #len])" @ "shr_ref (Vec_ty {T}) {'a}")]
    #[rr::returns("l" @ "alias_ptr_t")]
    fn ptr<'a>(&'a self) -> *mut T {
        self.buf.ptr() as *mut T
    }

    // private function, take an unfolded type
    #[rr::params("l" : "loc", "cap" : "nat", "len" : "Z")]
    #[rr::args(#raw "#(-[#(l, cap); #len])" @ "shr_ref (Vec_ty {T}) {'a}")]
    #[rr::returns("cap")]
    fn cap<'a>(&'a self) -> usize {
        self.buf.cap
    }

    #[rr::params("xs")]
    #[rr::args("#xs")]
    #[rr::returns("length xs")]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rr::returns("[]")]
    pub fn new() -> Self {
        Vec {
            buf: RawVec::new(),
            len: 0,
        }
    }

    #[rr::params("xs", "γ", "x")]
    #[rr::args("(#xs, γ)", "x")]
    #[rr::requires("Hlen_cap": "(length xs < MaxInt usize_t)%Z")]
    #[rr::requires("Hsz": "(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ MaxInt isize_t)%Z")]
    #[rr::observe("γ": "xs ++ [ #x]")]
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
    }

    #[rr::params("xs", "γ")]
    #[rr::args("(#(<#> xs), γ)")]
    #[rr::returns("<#>@{option} (last xs)")]
    #[rr::observe("γ": "(take (length xs - 1) (<#> xs))")]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(ptr::read(rrptr::mut_add(self.ptr(), self.len))) }
        }
    }

    // Not currently verified
    #[rr::trust_me]
    #[rr::params("xs", "γ", "i" : "nat", "x")]
    #[rr::args("(#(<#>xs), γ)", "Z.of_nat i", "x")]
    #[rr::requires("i ≤ length xs")]
    #[rr::requires("(length xs < max_int usize_t)%Z")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ max_int isize_t)%Z")]
    #[rr::observe("γ": "(<#> take i xs) ++ [ #x] ++ (<#> drop i xs)")]
    pub fn insert(&mut self, index: usize, elem: T) {
        // index out of bounds?
        assert!(index <= self.len);
        if self.cap() == self.len {
            self.buf.grow();
        }

        unsafe {
            // doing a memmove, effectively
            // we will want to spec this in terms of our array type
            ptr::copy(
                rrptr::mut_add(self.ptr(), index),
                rrptr::mut_add(self.ptr(), index + 1),
                self.len - index,
            );
            ptr::write(rrptr::mut_add(self.ptr(), index), elem);
            self.len += 1;
        }
    }

    // Not currently verified
    #[rr::trust_me]
    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::observe("γ": "delete i (<#> xs)")]
    pub fn remove(&mut self, index: usize) -> T {
        // index out of bounds?
        assert!(index < self.len);
        unsafe {
            self.len -= 1;
            let result = ptr::read(rrptr::mut_add(self.ptr(), index));
            // memmove
            ptr::copy(
                rrptr::mut_add(self.ptr(), index + 1),
                rrptr::mut_add(self.ptr(), index),
                self.len - index,
            );
            result
        }
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::requires("Hi": "i < length xs")]
    #[rr::exists("γi")]
    #[rr::returns("(#(xs !!! i), γi)")]
    #[rr::observe("γ": "<[i := PlaceGhost γi]> (<#> xs)")]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        self.len;
        unsafe {
            let p = rrptr::mut_add(self.ptr(), index);
            let ret = &mut *p;
            ret
        }
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::exists("γi", "γ1", "γ2")]
    #[rr::observe("γ2": "if decide (i < length xs) then <[i := PlaceGhost γ1]> (<#> xs) else <#> xs")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i), γi)) else None")]
    // NOTE: currently, we need a slightly more complicated specification that explicitly closes
    // under ghost variable equivalence: the "Inherit" part states that, after 'a has ended, the
    // ghost variables will have identical values
    #[rr::ensures(#iris "if decide (i < length xs) then Inherit {'a} InheritGhost (Rel2 γ2 γ (eq (A:=list (place_rfn T_rt)))) else True")]
    #[rr::ensures(#iris "if decide (i < length xs) then Inherit {'a} InheritGhost (Rel2 γi γ1 (eq (A:=T_rt))) else True")]
    pub fn get_mut<'a>(&'a mut self, index: usize) -> Option<&'a mut T> {
        if index < self.len() {
            unsafe { Some (self.get_unchecked_mut(index)) }
        }
        else {
            None
        }
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(<#> xs)", "Z.of_nat i")]
    #[rr::requires("Hi": "i < length xs")]
    #[rr::returns("#(xs !!! i)")]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.len;
        unsafe {
            let p = rrptr::mut_add(self.ptr(), index);
            let ret = &*p;
            ret
        }
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(<#> xs)", "Z.of_nat i")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i))) else None")]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            unsafe { Some (self.get_unchecked(index)) }
        }
        else {
            None
        }
    }
}
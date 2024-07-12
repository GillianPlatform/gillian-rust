use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;

pub struct GillianAllocator;

#[gillian::no_translate]
#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::alloc::alloc_array"]
pub fn alloc_array<T>(_len: usize) -> *mut T {
    unreachable!()
}

#[gillian::no_translate]
#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::alloc::dealloc_array"]
pub fn dealloc_array<T>(_ptr: *mut T, _len: usize) -> *mut T {
    unreachable!()
}

#[allow(unused_variables)]
unsafe impl Allocator for GillianAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // Implemented in GIL
        panic!()
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: Layout) {
        // Implemented in GIL
        panic!()
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // Implemented in GIL
        panic!()
    }
}

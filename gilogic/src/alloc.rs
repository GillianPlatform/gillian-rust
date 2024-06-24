use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;

pub struct GillianAllocator;

#[allow(unused_variables)]
unsafe impl Allocator for GillianAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        panic!("Implemented in GIL")
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: Layout) {
        panic!("Implemented in GIL")
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        panic!("Implemented in GIL")
    }
}

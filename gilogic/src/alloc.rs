use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;

pub struct GillianAllocator;

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

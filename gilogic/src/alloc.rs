use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;

pub struct GillianAllocator;

unsafe impl Allocator for GillianAllocator {
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        panic!("Implemented in GIL")
    }

    unsafe fn deallocate(&self, _ptr: std::ptr::NonNull<u8>, _layout: Layout) {
        panic!("Implemented in GIL")
    }

    fn allocate_zeroed(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        panic!("Implemented in GIL")
    }
}

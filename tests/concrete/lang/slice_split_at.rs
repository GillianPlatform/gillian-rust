#![no_std]

unsafe fn slice_from_raw_parts<'a>(ptr: *const u32, len: usize) -> &'a [u32] {
    &*core::ptr::slice_from_raw_parts(ptr, len)
}

fn split_at(slice: &[u32], mid: usize) -> (&[u32], &[u32]) {
    let len = slice.len();
    // let ptr = slice.as_ptr(); Replaced by its implementation below.
    let ptr = slice as *const [u32] as *const u32;
    unsafe {
        (
            slice_from_raw_parts(ptr, mid),
            slice_from_raw_parts(ptr.add(mid), len - mid),
        )
    }
}

pub fn main() -> u32 {
    let arr: [u32; 4] = [1, 2, 3, 4];
    let (left, right) = split_at(&arr, 2);
    left[0] + left[1] + right[0] + right[1] // ENDSWITH: 10i
}

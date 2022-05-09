fn split_at(slice: &[u32], mid: usize) -> (&[u32], &[u32]) {
    let len = slice.len();
    // let ptr = slice.as_ptr(); Replaced by its implementation below.
    let ptr = slice as *mut [u32] as *mut u32;
    unsafe {
        (
            slice::from_raw_parts(ptr, mid),
            slice::from_raw_parts(ptr.add(mid), len - mid)
        )
    }
}

pub fn main() {
    let arr : [u32; 4] = [1; 2; 3; 4];
    let (left, right) = split_at(&arr, 2);
}
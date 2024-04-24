#![no_std]

#[repr(C)]
struct A {
    x: u8,
    y: u16,
    z: u32,
}

pub fn main() -> u16 {
    let a = A {
        x: 13,
        y: 987,
        z: 343,
    };

    let p = &a.x as *const u8;
    let pp = unsafe { p.add(2) };
    unsafe { *(pp as *const u16) }
    // ENDSWITH: 987i
}

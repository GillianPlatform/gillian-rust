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

    a.y
    // ENDSWITH: 987i
}

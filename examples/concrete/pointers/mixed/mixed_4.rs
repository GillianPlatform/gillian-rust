#![no_std]

struct R8 {
    x: u8,
}

struct R64 {
    x: u64,
}

#[repr(C)]
struct C8 {
    x: u8,
}

#[repr(C)]
struct C16 {
    x: u16,
}

#[repr(C)]
struct A {
    x: R8,
    y: R64,
}

#[repr(C)]
struct B {
    x: A,
    y: R64,
}

struct C {
    x: [R8; 2],
    y: [R8; 2],
}

#[repr(C)]
struct D {
    x: C,
    y: R8,
}

#[repr(C)]
struct E {
    x: u8,
    y: R64,
}

#[repr(C)]
struct F {
    x: E,
    y: R64,
}

pub fn main() -> R64 {
    let f = F {
        x: E {
            x: 1,
            y: R64 { x: 2 },
        },
        y: R64 { x: 3 },
    };

    let p = &f.x.y as *const R64;
    unsafe { *(p.add(1)) }
    // ENDSWITH: {{ "R64", {{ 3i }} }}
}

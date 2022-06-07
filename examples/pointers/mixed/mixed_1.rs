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

pub fn main() -> R8 {
    let t: [A; 2] = [
        A {
            x: R8 { x: 1 },
            y: R64 { x: 2 },
        },
        A {
            x: R8 { x: 3 },
            y: R64 { x: 4 },
        },
    ];

    let p = &t[0].x as *const R8 as *const A;
    unsafe { *((p.add(1)) as *const R8) }
    // ENDSWITH: {{ "R8", {{ 3i }} }}
}

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

pub fn main() -> R8 {
    let d = D {
        x: C {
            x: [R8 { x: 1 }, R8 { x: 2 }],
            y: [R8 { x: 3 }, R8 { x: 4 }],
        },
        y: R8 { x: 5 },
    };

    let p = &d.x.x[0] as *const R8;
    unsafe { *(p.add(4)) }
    // ENDSWITH: {{ "R8", {{ 5i }} }}
}

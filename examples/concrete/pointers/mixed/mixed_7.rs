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
#[repr(C)]
struct G {
    x: R64,
    y: u16,
    z: u8,
}

#[repr(C)]
struct H {
    x: R64,
    y: C16,
    z: C8,
}

pub fn main() -> C8 {
    let h = H {
        x: R64 { x: 1 },
        y: C16 { x: 2 },
        z: C8 { x: 3 },
    };
    let p = &h.y as *const C16;
    unsafe { *(p.add(1) as *const C8) }
    // ENDSWITH: {{ "C8", {{ 3i }} }}
}

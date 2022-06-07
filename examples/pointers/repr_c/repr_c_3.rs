#![no_std]

#[repr(C)]
struct A {
    x: u8,
    y: u16,
    z: u32,
}

#[repr(C)]
struct B {
    x: A,
    y: C,
}

#[repr(C)]
struct C {
    x: [u8; 5],
    y: [A; 5],
}

fn makeC() -> C {
    let x = [0, 1, 2, 3, 4];
    let y = [
        A { x: 5, y: 6, z: 7 },
        A { x: 8, y: 9, z: 10 },
        A {
            x: 11,
            y: 12,
            z: 13,
        },
        A {
            x: 14,
            y: 15,
            z: 16,
        },
        A {
            x: 17,
            y: 18,
            z: 19,
        },
    ];
    C { x, y }
}

fn makeB() -> B {
    let x = A {
        x: 250,
        y: 251,
        z: 252,
    };
    B { x, y: makeC() }
}

pub fn main() -> u8 {
    let b = makeB();

    b.y.y[3].x
    // ENDSWITH: 14i
}

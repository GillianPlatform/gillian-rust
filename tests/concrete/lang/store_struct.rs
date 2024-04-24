#![no_std]

struct A {
    u: i32,
    v: i32,
}

pub fn main() -> A {
    let mut x = A { u: 1, v: 2 };
    x.v = 1000;
    x // ENDSWITH: {{ 1i, 1000i }}
}

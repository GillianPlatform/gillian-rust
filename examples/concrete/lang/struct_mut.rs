#![no_std]

struct A {
    u: i32,
    v: i32,
}

fn modify(x: &mut A) {
    x.v = 1000;
}

pub fn main() -> A {
    let mut x: A = A { u: 1, v: 2 };
    modify(&mut x);
    x // ENDSWITH: {{ 1i, 1000i }}
}

#![no_std]
struct A {
    v: i32,
}

fn test(u: A, v: A) -> i32 {
    let mut x: (A, A) = (u, v);
    let sec: *const A = &x.1;
    x.0 = x.1;
    unsafe { (*sec).v }
}

pub fn main() {
    let u: A = A { v: 1 };
    let v: A = A { v: 2 };
    let _ret = test(u, v);
}

#![no_std]

pub fn add_four(x: &mut i32) -> i32 {
    *x += 7;
    (*x) + 4
}

pub fn main() {
    let mut z = 4;
    let _y = add_four(&mut z);
}

#![no_std]

pub fn add_four(x: &i32) -> i32 {
    (*x) + 4
}

pub fn main() -> i32 {
    let z = 4;
    add_four(&z) // ENDSWITH: 8i
}

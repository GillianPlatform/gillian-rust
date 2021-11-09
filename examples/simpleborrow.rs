#![no_std]

pub fn add_four(x: &i32) -> i32 {
    (*x) + 4
}

pub fn test() {
    let z = 4;
    let _y = add_four(&z);
}

#![no_std]

fn add_four(x: i32) -> i32 {
    x + 4
}

pub fn main() {
    let x = 3;
    let z = add_four(x);
    let _y = x + z;
    // x = 3
    // z = 7
    // _y = 10
}

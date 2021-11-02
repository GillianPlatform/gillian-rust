#![no_std]

fn add_four(x: i32) -> i32 {
    x + 4
}

pub fn test() {
    let x = 3;
    let z = add_four(x);
    let _y = x + z;
}

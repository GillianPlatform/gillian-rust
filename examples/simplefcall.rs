#![no_std]

fn seven() -> i32 {
    let x = 4;
    let y = 3;
    x + y
}

pub fn main() {
    let _x = seven();
}

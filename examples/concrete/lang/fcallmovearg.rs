#![no_std]

fn add_four(x: i32) -> i32 {
    x + 4
}

pub fn main() -> (i32, i32, i32) {
    let x = 3;
    let z = add_four(x);
    let y = x + z;
    (x, y, z) // ENDSWITH: {{ 3i, 10i, 7i }}
}

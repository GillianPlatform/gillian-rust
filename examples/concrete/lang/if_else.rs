#![no_std]

pub fn main() -> i32 {
    let x = 4;
    let mut y = 10;
    if x > 10 {
        y = 0
    } else {
        y = 10000
    }
    y // ENDSWITH: 10000i
}

#![no_std]

pub fn mutate(x: &mut i32) {
    *x += 7
}

pub fn main() {
    let mut z = 4;
    mutate(&mut z);
}

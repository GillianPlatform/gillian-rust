#![no_std]

pub fn mutate(x: &mut i32) {
    *x += 7
}

pub fn main() -> i32 {
    let mut z = 4;
    mutate(&mut z);
    z // ENDSWITH: 11i
}

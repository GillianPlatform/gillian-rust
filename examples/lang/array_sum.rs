#![no_std]

fn sum(x: &[u32]) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < x.len() {
        s += x[i];
        i += 1;
    }
    s
}

pub fn main() -> u32 {
    let x: [u32; 4] = [1, 2, 3, 4];
    sum(&x) // ENDSWITH: 10i
}

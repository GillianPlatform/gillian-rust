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

fn sum_4(x: &[u32; 4]) -> u32 {
    x[0] + x[1] + x[2] + x[3]
}

pub fn main() {
    let x: [u32; 4] = [1, 2, 3, 4];
    let _s = sum(&x);
    let _s2 = sum_4(&x);
}

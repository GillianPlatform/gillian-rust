#![no_std]

pub fn test() {
    let mut x = ((1, 2), (3, 4, (5, 6)));
    x.1 .2 .0 = 12;
}

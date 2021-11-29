#![no_std]

type Something = (i32, i32, (i32, i32));

pub fn modify(x: &mut Something) {
    x.2 .0 = 12;
}

pub fn main() {
    let mut x: ((i32, i32), Something) = ((1, 2), (3, 4, (5, 6)));
    modify(&mut x.1);
    x.0 .0 = 1000;
}

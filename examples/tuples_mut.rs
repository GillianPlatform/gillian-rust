#![no_std]

type Something = (i32, i32, (i32, i32));

pub fn modify(x: &mut Something) {
    x.2 .0 = 12;
}

pub fn test() {
    let mut x: ((i32, i32), Something) = ((1, 2), (3, 4, (5, 6)));
    modify(&mut x.1);
    x.1 .2 .0 = 12;
}

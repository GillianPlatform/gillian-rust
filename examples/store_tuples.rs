#![no_std]

pub fn main() -> ((i32, i32), (i32, i32, (i32, i32))) {
    let mut x = ((1, 2), (3, 4, (5, 6)));
    x.1 .2 .0 = 12;
    x // ENDSWITH: {{ {{ 1i, 2i }}, {{ 3i, 4i, {{ 12i, 6i }} }} }}
}

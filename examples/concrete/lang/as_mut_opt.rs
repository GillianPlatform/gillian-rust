fn main() -> Option<u32> {
    let mut x = Some(12);
    test(&mut x);
    x
} // ENDSWITH: {{ 1i, {{ 0i }} }}

fn as_mut(y: &mut Option<u32>) -> Option<&mut u32> {
    match *y {
        Some(ref mut x) => Some(x),
        None => None,
    }
}

fn test(x: &mut Option<u32>) {
    match as_mut(x) {
        None => (),
        Some(z) => *z = 0,
    }
}

#![no_std]
use core::panic::PanicInfo;

fn add_four(x: i32) -> i32 {
    x + 4
}

pub fn test() {
    let x = 3;
    let _z = add_four(x);
    let _y = x + _z;
}

#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

#![no_std]
use core::panic::PanicInfo;

fn add_four(x: i32) -> i32 {
    x + 4
}

pub fn test() {
    let x = 3;
    let z = add_four(x);
    let _y = x + z;
}

#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

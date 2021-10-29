#![no_std]
use core::panic::PanicInfo;

pub fn test() -> isize {
    let x = 4;
    let z = x + 3;
    z
}

#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

#![no_std]
use core::panic::PanicInfo;

fn seven() -> i32 {
    let x = 4;
    let y = 3;
    x + y
}

pub fn test() {
    let _x = seven();
}

#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

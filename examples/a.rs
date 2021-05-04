#![no_std]
use core::panic::PanicInfo;

#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

fn main() {
    let _x = do_something();
}

fn do_something() -> isize {
    3
}
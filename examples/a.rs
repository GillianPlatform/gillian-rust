#![no_std]
use core::panic::PanicInfo;

fn main(){
    let x = 4;
    let _z = x + 3;
}


#[panic_handler]
fn panic(_panic: &PanicInfo<'_>) -> ! {
    loop {}
}

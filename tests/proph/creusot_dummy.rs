//@check-pass
extern crate creusillian;
extern crate gilogic;

use gilogic::prophecies::{Prophecised, Ownable};
use gilogic::mutref_auto_resolve;

#[creusillian::ensures(ret == 4u32)]
pub fn test() -> u32 {
    4
}


#[creusillian::ensures({let x = ret == 4u32; x})]
pub fn test2() -> u32 {
    4
}



#[creusillian::ensures(match x { Some(a) => ret == a, None => ret == 0u32})]
pub fn test3(x : Option<u32>) -> u32 {
    match x {
        Some(x) => x,
        None => 0,
    }
}

#[creusillian::requires(*x == 0)]
#[creusillian::ensures(^x == 1)]
pub fn write(x : &mut u32) {
    *x = 1;
    mutref_auto_resolve!(x);
}


#[creusillian::requires(*x@ == 0)]
#[creusillian::ensures(^x == 1)]
pub fn write2(x : &mut u32) {
    *x = 1;
    mutref_auto_resolve!(x);
}


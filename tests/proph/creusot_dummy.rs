//@check-pass
extern crate creusillian;
extern crate gilogic;

use gilogic::prophecies::Ownable;
use gilogic::macros::specification;

// #[creusillian::ensures(ret == 4u32)]
// fn test() -> u32 {
//     4
// }


// #[creusillian::ensures({let x = ret == 4u32; x})]
// fn test2() -> u32 {
//     4
// }



// #[creusillian::ensures(match x { Some(a) => ret == a, None => ret == 0u32})]
#[specification(requires { emp } 
exists ret_repr.
ensures {
    ret.own(ret_repr) * $ (exists < x : bool > true) $
})]
fn test3(x : Option<u32>) -> u32 {
    match x {
        Some(x) => x,
        None => 0,
    }
}
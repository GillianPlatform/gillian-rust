extern crate creusillian;
extern crate gilogic;

#[creusillian::ensures(ret == 4u32)]
fn test() -> u32 {
    4
}

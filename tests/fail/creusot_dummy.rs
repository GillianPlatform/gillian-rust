extern crate creusillian;
extern crate gilogic;

#[creusillian::ensures(@ret == 4)]
fn test() -> u32 {
    4
}

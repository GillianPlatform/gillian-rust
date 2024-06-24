extern crate creusillian;
extern crate gilogic;

#[creusillian::ensures(ret == 4u32)]
fn test() -> u32 {
    4
}


#[creusillian::ensures({let x = ret == 4u32; x})]
fn test2() -> u32 {
    4
}



#[creusillian::ensures(match x { Some(a) => res == a, None => res == 0u32})]
fn test3(x : Option<u32>) -> u32 {
    match x {
        Some(x) => x,
        None => 0,
    }
}

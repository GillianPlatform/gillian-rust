#![no_std]

enum MyEnum {
    X,
    Y,
}

fn test(x: MyEnum) -> i32 {
    match x {
        MyEnum::X => 1,
        MyEnum::Y => 1000,
    }
}

pub fn main() {
    let x = MyEnum::X;
    let y = MyEnum::Y;
    let _e = test(x) + test(y);
}

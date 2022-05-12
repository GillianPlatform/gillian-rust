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

fn modify(x: &mut MyEnum) {
    *x = MyEnum::Y;
}

pub fn main() -> i32 {
    let mut x = MyEnum::X;
    modify(&mut x);
    let y = MyEnum::Y;
    test(x) + test(y) // ENDSWITH: 2000i
}

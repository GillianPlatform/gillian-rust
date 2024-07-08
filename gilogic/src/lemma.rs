#[macro_export]
macro_rules! package {
    ($x:expr, $y:expr) => {
        gilogic::__stubs::package($x, $y)
    };
}

#[macro_export]
macro_rules! assert_bind {
    ($($x:ident),* | $e:expr ) => {
        ()
    };
}

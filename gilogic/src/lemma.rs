#[macro_export]
macro_rules! package {
    ($x:expr, $y:expr) => {
        gilogic::__stubs::package($x, $y)
    };
}

#[macro_export]
macro_rules! assume {
    ($t:tt) => {
        gilogic::__stubs::assume(gilogic::macros::formula!($t))
    };
}

#[macro_export]
macro_rules! unfold {
	($f:ident ($($x:expr),*)) => {
		gilogic :: __stubs :: unfold_proof ( $f ($($x),*) )
	}
}

#[macro_export]
macro_rules! fold {
	($f:ident ($($x:expr),*)) => {
		gilogic :: __stubs :: fold_proof ( $f ($($x),*) )
	}
}

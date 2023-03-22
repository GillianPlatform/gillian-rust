macro_rules! get_thir {
    ($thir:pat, $expr:pat, $s:expr) => {
        let ___thir = $s.tcx.thir_body(WithOptConstParam::unknown(
            $s.did().as_local().expect("non-local predicate"),
        ));
        let ($thir, $expr) = if let Ok((___thir, ___expr)) = ___thir {
            (___thir.borrow(), ___expr)
        } else {
            fatal!($s, "Predicate body failed to typecheck for {:?}", $s.did())
        };
    };
}

pub(crate) use get_thir;

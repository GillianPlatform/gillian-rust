macro_rules! get_thir {
    ($s:expr) => {
        get_thir!($s, $s.did())
    };

    ($s:expr, $did:expr) => {{
        let ___thir = $s.tcx().thir_body(WithOptConstParam::unknown(
            $did.as_local().expect("non-local predicate"),
        ));
        if let Ok((___thir, ___expr)) = ___thir {
            (___thir.borrow(), ___expr)
        } else {
            fatal!($s, "Predicate body failed to typecheck for {:?}", $s.did())
        }
    }};
}

pub(crate) use get_thir;

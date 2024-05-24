macro_rules! get_thir {
    ($s:expr) => {
        get_thir!($s, $s.did())
    };

    ($s:expr, $did:expr) => {{
        let ___thir = $s.tcx().thir_body($did.as_local().unwrap_or_else(|| {
            crate::prelude::fatal!(
                $s,
                "non-local predicate {:?}",
                $s.global_env().just_pred_name($did)
            )
        }));
        match ___thir {
            Ok((thir, expr)) => (thir.borrow(), expr),
            Err(e) => crate::prelude::fatal!(
                $s,
                "Predicate body failed to typecheck for {:?} {e:?}",
                $did
            ),
        }
    }};
}

pub(crate) use get_thir;

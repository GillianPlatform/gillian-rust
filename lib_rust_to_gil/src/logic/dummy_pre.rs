use crate::{codegen::typ_encoding, prelude::*, utils::polymorphism::HasGenericArguments};

pub struct DummyPre<'tcx> {
    fn_did: DefId,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> HasDefId for DummyPre<'tcx> {
    fn did(&self) -> DefId {
        self.fn_did
    }
}

impl<'tcx> HasTyCtxt<'tcx> for DummyPre<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> DummyPre<'tcx> {
    pub fn new(fn_did: DefId, tcx: TyCtxt<'tcx>) -> Self {
        Self { fn_did, tcx }
    }
}

impl<'tcx> HasGenericArguments<'tcx> for DummyPre<'tcx> {}

impl<'tcx> From<DummyPre<'tcx>> for gillian::gil::Assertion {
    fn from(value: DummyPre<'tcx>) -> Self {
        value
            .generic_types()
            .into_iter()
            .map(|ty| {
                let name = typ_encoding::param_type_name(ty.0, ty.1);
                let lvar_name = format!("#{}", name);
                Assertion::Pure(Formula::eq(Expr::PVar(name), Expr::LVar(lvar_name)))
            })
            .collect()
    }
}

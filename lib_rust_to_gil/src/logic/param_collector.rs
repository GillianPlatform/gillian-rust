use std::ops::ControlFlow;

use crate::prelude::*;
use rustc_middle::ty::Region;
use rustc_type_ir::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor};

#[derive(Debug)]
pub struct ParamCollector<'tcx> {
    pub regions: bool,
    pub parameters: Vec<Ty<'tcx>>,
}

pub fn collect_params_on_args(args: GenericArgsRef) -> ParamCollector {
    let mut collector = ParamCollector::new();
    for arg in args {
        arg.visit_with(&mut collector);
    }
    collector
}

pub fn collect_params<'tcx, V>(v: V) -> ParamCollector<'tcx>
where
    V: TypeVisitable<TyCtxt<'tcx>>,
{
    let mut collector = ParamCollector::new();
    v.visit_with(&mut collector);
    collector
}

impl<'tcx> ParamCollector<'tcx> {
    pub fn new() -> Self {
        Self {
            regions: false,
            parameters: vec![],
        }
    }

    pub fn with_consider_arguments<I>(mut self, it: I) -> Self
    where
        I: Iterator<Item = Ty<'tcx>>,
    {
        for ty in it {
            if ty.is_ref() {
                self.regions = true;
                break;
            }
        }
        self
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for ParamCollector<'tcx> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let TyKind::Param(_) = *t.kind() {
            self.parameters.push(t);
        }
        t.super_visit_with(self)
    }

    fn visit_region(&mut self, _r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        self.regions = true;
        ControlFlow::Continue(())
    }
}

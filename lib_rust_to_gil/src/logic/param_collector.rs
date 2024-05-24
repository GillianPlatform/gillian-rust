use crate::prelude::*;
use indexmap::IndexSet;
use rustc_middle::ty::{ParamTy, Region};
use rustc_type_ir::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor};

#[derive(Debug)]
pub struct ParamCollector {
    pub parameters: IndexSet<ParamTy>,
}

pub fn collect_params_on_args(args: GenericArgsRef) -> ParamCollector {
    let mut collector = ParamCollector::new();
    for arg in args {
        arg.visit_with(&mut collector);
    }
    collector
}

pub fn collect_params<'tcx, V>(v: V) -> impl Iterator<Item = ParamTy>
where
    V: TypeVisitable<TyCtxt<'tcx>>,
{
    let mut collector = ParamCollector::new();
    v.visit_with(&mut collector);
    collector.parameters.into_iter()
}

pub fn collect_regions<'tcx, V>(v: V) -> RegionsCollector<'tcx>
where
    V: TypeVisitable<TyCtxt<'tcx>>,
{
    let mut collector = RegionsCollector::default();
    v.visit_with(&mut collector);
    collector
}

#[derive(Debug, Default)]
pub struct RegionsCollector<'tcx> {
    pub regions: IndexSet<Region<'tcx>>,
}

impl ParamCollector {
    pub fn new() -> Self {
        Self {
            parameters: Default::default(),
        }
    }

    pub fn with_consider_arguments<'tcx, I>(self, it: I) -> Self
    where
        I: Iterator<Item = Ty<'tcx>>,
    {
        for ty in it {
            if ty.is_ref() {
                break;
            }
        }
        self
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for ParamCollector {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> Self::Result {
        if let TyKind::Param(pty) = *t.kind() {
            self.parameters.insert(pty);
        }
        t.super_visit_with(self)
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for RegionsCollector<'tcx> {
    fn visit_region(&mut self, _r: Region<'tcx>) -> Self::Result {
        self.regions.insert(_r);
    }
}

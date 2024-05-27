use std::collections::HashMap;

use gillian::gil::{Assertion, Expr, Flag, Formula, SingleSpec, Spec, Type};

use indexmap::IndexSet;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgsRef, Ty, TyCtxt};
use rustc_span::Symbol;

use crate::{
    codegen::typ_encoding::{lifetime_param_name, type_param_name},
    logic::{
        param_collector::{collect_params, collect_regions},
        PredCtx,
    },
    prelude::{ty_utils, GlobalEnv, HasTyCtxt},
    temp_gen::{self, TempGenerator},
    utils::attrs::{is_lemma, is_predicate},
};
use rustc_data_structures::captures::Captures;

// TODO: Track in parameters
// TODO: Trakc the kind of item this is
#[derive(Debug)]
pub struct Signature<'tcx> {
    // pub name: Symbol,
    pub args: Vec<ParamKind<'tcx>>,
    contract: Option<Contract<'tcx>>,
}

#[derive(Debug)]
struct Contract<'tcx> {
    pre: Assertion,
    post: (Vec<(Symbol, Ty<'tcx>)>, Assertion),
}

#[derive(Debug, Clone)]
pub enum ParamKind<'tcx> {
    Program(Symbol, Ty<'tcx>),
    Lifetime(Symbol),
    Generic(Symbol),
    Logic(Symbol, Ty<'tcx>),
}

impl<'tcx> ParamKind<'tcx> {
    pub fn name(&self) -> Symbol {
        match self {
            ParamKind::Program(n, _) => *n,
            ParamKind::Lifetime(n) => *n,
            ParamKind::Generic(n) => *n,
            ParamKind::Logic(n, _) => *n,
        }
    }
}

impl<'tcx> Signature<'tcx> {
    /// Returns all *universally* quantified program or logic variables
    pub fn all_vars(&self) -> impl Iterator<Item = (Symbol, Ty<'tcx>)> + '_ {
        self.args.iter().filter_map(move |arg| match arg {
            ParamKind::Program(nm, ty) => Some((*nm, *ty)),
            ParamKind::Logic(nm, ty) => Some((*nm, *ty)),
            _ => None,
        })
    }

    /// Returns all lifetimes. Currently conflates 'early' and 'latebound' lifetimes
    pub fn lifetimes(&self) -> impl Iterator<Item = Symbol> + '_ + Captures<'tcx> {
        self.args.iter().filter_map(move |arg| match arg {
            ParamKind::Lifetime(nm) => Some(*nm),
            _ => None,
        })
    }

    /// Returns all type parameters.
    pub fn type_params(&self) -> impl Iterator<Item = Symbol> + '_ + Captures<'tcx> {
        self.args.iter().filter_map(move |arg| match arg {
            ParamKind::Generic(nm) => Some(*nm),
            _ => None,
        })
    }

    /// Return the "physical arguments" of a symbol, ak everything except the lvars.
    pub fn physical_args(&self) -> impl Iterator<Item = ParamKind<'tcx>> + '_ {
        self.args
            .iter()
            .filter(|a| !matches!(a, ParamKind::Logic(_, _)))
            .cloned()
    }

    /// Returns the set of type well-formedness assertions for the input parameters of a predicate
    pub fn type_wf_pres(
        &self,
        ctx: &mut GlobalEnv<'tcx>,
        temp: &mut TempGenerator,
    ) -> Vec<Assertion> {
        let mut wfs = Vec::new();
        for (nm, ty) in self.all_vars() {
            let lvar = Expr::LVar(format!("#{nm}"));
            wfs.push(make_wf_asrt(ctx, temp, lvar, ty));
        }

        wfs
    }

    /// Asserts that inputs equal their respective lvars. Something to do with the 'mutable store' according to sacha
    pub fn store_eq_var(&self) -> Vec<Assertion> {
        let mut wfs = Vec::new();

        for (nm, _) in self.all_vars() {
            let lvar = Expr::LVar(format!("#{nm}"));
            wfs.push(Expr::PVar(nm.to_string()).eq_f(lvar).into_asrt());
        }
        wfs
    }

    /// Asserts that inputs equal their respective lvars. Something to do with the 'mutable store' according to sacha
    pub fn store_eq_all(&self) -> Vec<Assertion> {
        let mut wfs = Vec::new();

        for arg in &self.args {
            let name = arg.name();
            let lvar = Expr::LVar(format!("#{}", name));
            wfs.push(Expr::PVar(name.to_string()).eq_f(lvar).into_asrt());
        }
        wfs
    }

    /// Returns the user-provided precondition of this item
    pub fn user_pre(&self) -> Option<&Assertion> {
        Some(&self.contract.as_ref()?.pre)
    }

    /// Returns the user-provided postcondition of this item
    pub fn user_post(&self, temp: &mut TempGenerator) -> Option<Assertion> {
        let subst: HashMap<_, _> = self
            .contract
            .as_ref()?
            .post
            .0
            .iter()
            .map(|lvar| (lvar.0.to_string(), Expr::LVar(temp.fresh_lvar())))
            .collect();
        let mut post = self.contract.as_ref()?.post.1.clone();

        post.subst_lvar(&subst);
        Some(post)
    }

    /// Returns a precondition elaborated with well-formedness and mutable-store assertions
    fn full_pre(&self, ctx: &mut GlobalEnv<'tcx>, temp: &mut TempGenerator) -> Option<Assertion> {
        let mut wf = self.type_wf_pres(ctx, temp);
        let lv = self.store_eq_all();
        let mut pre = self.contract.as_ref()?.pre.clone();
        // HACK(xavier): substitute program vars for their lvars here. Doing it elsewhere
        // would require first refactoring all of `predicate.rs` which... lets wait for another day

        let var_map = self
            .args
            .iter()
            .filter_map(|pk| match pk {
                ParamKind::Program(nm, _) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Lifetime(nm) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Generic(nm) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Logic(_, _) => None,
            })
            .collect();

        pre.subst_pvar(&var_map);

        for lft in self.lifetimes() {
            let lvar = Expr::LVar(format!("#{lft}"));
            wf.push(crate::logic::core_preds::alive_lft(lvar));
        }

        let full_pre = lv.into_iter().chain(wf).rfold(pre, Assertion::star);

        Some(full_pre)
    }

    // TODO(xavier): Use `user_post` here to avoid hygiene issues!!!!!!
    fn full_post(&self) -> Option<Assertion> {
        let mut wf = Vec::new();
        let mut post = self.contract.as_ref()?.post.1.clone();
        for lft in self.lifetimes() {
            let lvar = Expr::LVar(format!("#{lft}"));
            wf.push(crate::logic::core_preds::alive_lft(lvar));
        }

        let var_map = self
            .args
            .iter()
            .filter_map(|pk| match pk {
                ParamKind::Program(nm, _) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Lifetime(nm) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Generic(nm) => Some((nm.to_string(), Expr::LVar(format!("#{nm}")))),
                ParamKind::Logic(_, _) => None,
            })
            .collect();

        post.subst_pvar(&var_map);

        Some(wf.into_iter().rfold(post, Assertion::star))
    }

    /// Return a gil spec for a procedure corresponding to this signature
    pub fn to_gil_spec(self, ctx: &mut GlobalEnv<'tcx>, name: String) -> Option<Spec> {
        let mut temp = TempGenerator::new();

        let sspec = SingleSpec {
            pre: self.full_pre(ctx, &mut temp)?,
            posts: vec![self.full_post()?],
            flag: Flag::Normal,
        };
        Some(Spec {
            params: self
                .args
                .into_iter()
                .map(|a| a.name().to_string())
                .collect(),
            name,
            sspecs: vec![sspec],
        })
    }
}

pub fn build_signature<'tcx>(
    global_env: &mut GlobalEnv<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Signature<'tcx> {
    assert!(
        matches!(
            global_env.tcx().def_kind(id),
            DefKind::Fn | DefKind::AssocFn
        ),
        "{:?}",
        global_env.tcx().def_kind(id)
    );
    let tcx = global_env.tcx();

    // TODO: Fix, this is wrong in a context where we are building a substitution for an (id, subst) pair, consider
    // the case of a function `fn<T>(..)` where we apply `T = (U, V)`, we should build something which looks more like `fn<U,V>`.
    // This means I don't think we want to use the generics at all?

    let mut args = Vec::new();
    let sig = tcx.fn_sig(id).instantiate(tcx, subst);

    let mut regions = collect_regions(sig.inputs()).regions;
    regions.extend(collect_regions(sig.output()).regions);
    for (ix, r) in regions.iter().enumerate() {
        match r.kind() {
            rustc_type_ir::RegionKind::ReVar(_) => todo!("re var??"),
            rustc_type_ir::RegionKind::ReErased => args.push(ParamKind::Lifetime(Symbol::intern(
                &lifetime_param_name("erased"),
            ))),
            rustc_type_ir::RegionKind::ReBound(_, _) => {
                let nm = if let Some(nm) = r.get_name() {
                    lifetime_param_name(&nm.as_str()[1..])
                } else {
                    lifetime_param_name(&ix.to_string())
                };
                args.push(ParamKind::Lifetime(Symbol::intern(&nm)));
            }
            rustc_type_ir::RegionKind::ReEarlyParam(_) => {
                let nm = if let Some(nm) = r.get_name() {
                    lifetime_param_name(&nm.as_str()[1..])
                } else {
                    lifetime_param_name(&ix.to_string())
                };
                args.push(ParamKind::Lifetime(Symbol::intern(&nm)));
            }
            rustc_type_ir::RegionKind::ReLateParam(_) => todo!("ReLateParam"),
            rustc_type_ir::RegionKind::ReStatic => todo!("ReStatic"),
            rustc_type_ir::RegionKind::RePlaceholder(_) => todo!("RePlaceHolder"),
            rustc_type_ir::RegionKind::ReError(_) => todo!("ReError"),
            // k => unreachable!("ILLEGAL REGION {k:?} {args:?}")
        }
    }

    let params: IndexSet<_> = collect_params(sig.inputs())
        .chain(collect_params(sig.output()))
        .collect();

    for pty in params {
        let arg = ParamKind::Generic(Symbol::intern(&type_param_name(pty.index, pty.name)));

        args.push(arg)
    }

    let fn_args = tcx
        .fn_arg_names(id)
        .iter()
        .enumerate()
        .zip(tcx.fn_sig(id).instantiate_identity().inputs().iter());

    let mut subst = HashMap::new();

    for ((_, nm), ty) in fn_args {
        let prog_name: Symbol = if is_lemma(id, tcx) || is_predicate(id, tcx) {
            nm.name
        } else {
            Symbol::intern(&format!("{}", nm))
        };
        args.push(ParamKind::Program(prog_name, *ty.skip_binder()));
        subst.insert(nm.name.to_string(), Expr::PVar(prog_name.to_string()));
    }

    let (uni_vars, contract) = if let Some(spec_id) = global_env.spec_map.get(&id) {
        let mut temp_gen = temp_gen::TempGenerator::new();

        let (uni, mut pre, mut post) =
            PredCtx::new_with_identity_args(global_env, &mut temp_gen, *spec_id).raw_spec();

        if !(is_lemma(id, tcx) || is_predicate(id, tcx)) {
            pre.subst_pvar(&subst);
            post.1.subst_pvar(&subst);
        }

        (uni, Some(Contract { pre, post }))
    } else {
        (Default::default(), None)
    };

    args.extend(
        uni_vars
            .into_iter()
            .map(|(nm, ty)| ParamKind::Logic(nm, ty)),
    );

    Signature { args, contract }
}

pub fn raw_ins(tcx: TyCtxt<'_>, id: DefId) -> Vec<usize> {
    let Some(ins_attr) = crate::utils::attrs::get_attr(
        tcx.get_attrs_unchecked(id),
        &["gillian", "decl", "pred_ins"],
    ) else {
        tcx.dcx()
            .fatal(format!("Predicate {id:?} doesn't have ins attribute"))
    };

    let Some(str_arg) = ins_attr.value_str() else {
        tcx.dcx().fatal("Predicate ins attribute must be a string")
    };
    let str_arg = str_arg.as_str().to_owned();

    if str_arg.is_empty() {
        return vec![];
    }
    str_arg
        .split(',')
        .map(|s| s.parse().expect("Ins should be a list of parameter number"))
        .collect()
}

fn make_wf_asrt<'tcx>(
    ctx: &mut GlobalEnv<'tcx>,
    temps: &mut TempGenerator,
    e: Expr,
    ty: Ty<'tcx>,
) -> Assertion {
    // The type here is already substituted
    if ty.is_any_ptr() {
        if ty_utils::is_mut_ref(ty) && ctx.config.prophecies {
            make_is_mut_ref_proph_ref_asrt(temps, e)
        } else {
            make_is_ptr_asrt(temps, e)
        }
    } else if ty.is_integral() {
        Assertion::Types(vec![(e, Type::IntType)])
    } else if is_nonnull(ctx.tcx(), ty) {
        make_is_nonnull_asrt(temps, e)
    } else if is_unique(ctx.tcx(), ty) {
        make_is_unique_asrt(temps, e)
    } else if crate::utils::ty::is_unsigned_integral(ty) {
        Formula::i_le(0, e).into_asrt()
    } else {
        Assertion::Emp
    }
}

fn is_nonnull<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    crate::utils::ty::is_nonnull(ty, tcx)
}

fn is_unique<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    crate::utils::ty::is_unique(ty, tcx)
}

// fn make_nonnull<'tcx>(tcx: TyCtxt<'tcx>, ptr: Expr) -> Expr {
//     [ptr].into()
// }

fn make_is_ptr_asrt(fresh: &mut TempGenerator, e: Expr) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    types.star(e.eq_f([loc, proj]).into_asrt())
}

fn make_is_nonnull_asrt(fresh: &mut TempGenerator, e: Expr) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    types.star(e.eq_f([Expr::EList(vec![loc, proj])]).into_asrt())
}

fn make_is_unique_asrt(fresh: &mut TempGenerator, e: Expr) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    types.star(
        e.eq_f([
            Expr::EList(vec![Expr::EList(vec![loc, proj])]),
            vec![].into(),
        ])
        .into_asrt(),
    )
}

fn make_is_mut_ref_proph_ref_asrt(fresh: &mut TempGenerator, e: Expr) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let pcy = temp_lvar(fresh);
    let pcy_proj = Expr::from(vec![]);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
        (pcy_proj.clone(), Type::ListType),
    ]);
    types.star(e.eq_f([[loc, proj], [pcy, pcy_proj]]).into_asrt())
}

fn temp_lvar(fresh: &mut TempGenerator) -> Expr {
    Expr::LVar(fresh.fresh_lvar())
}

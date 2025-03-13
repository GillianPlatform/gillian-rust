use std::{collections::HashMap, iter};

use gillian::gil::{Assertion, Expr, Flag, Formula, SingleSpec, Spec, Type};

use indexmap::IndexSet;
use rustc_hir::def_id::DefId;
use rustc_hir::{def::DefKind, Unsafety};
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{symbol, Symbol};

use crate::utils::attrs::{args_deferred, is_magic_closure};
use crate::{
    codegen::typ_encoding::{lifetime_param_name, type_param_name},
    logic::{
        param_collector::{collect_params, collect_regions},
        PredCtx,
    },
    prelude::{ty_utils, GlobalEnv, HasTyCtxt},
    temp_gen::TempGenerator,
    utils::attrs::{is_lemma, is_predicate},
};
use rustc_data_structures::captures::Captures;

// TODO: Track in parameters
// TODO: Trakc the kind of item this is
#[derive(Debug)]
pub struct Signature<'tcx, 'genv> {
    // pub name: Symbol,
    pub args: Vec<ParamKind<'tcx>>,
    contract: Option<Contract<'tcx>>,
    pub temp_gen: &'genv mut TempGenerator,
}

#[derive(Debug)]
struct Contract<'tcx> {
    timeless: bool,
    pre: Assertion,
    post: Vec<(Vec<(Symbol, Ty<'tcx>)>, Assertion)>,
    trusted: bool,
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

    pub fn as_lvar(&self) -> String {
        match self {
            ParamKind::Program(n, _) => format!("#{n}"),
            ParamKind::Lifetime(n) => format!("#{n}"),
            ParamKind::Generic(n) => format!("#{n}"),
            ParamKind::Logic(n, _) => format!("{n}"),
        }
    }
}

impl<'tcx, 'genv> Signature<'tcx, 'genv> {
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

    pub fn args(&self) -> impl Iterator<Item = ParamKind<'tcx>> + '_ {
        self.args.iter().cloned()
    }

    /// Returns the set of type well-formedness assertions for the input parameters of a predicate
    pub fn type_wf_pres(&mut self, ctx: &mut GlobalEnv<'tcx>) -> Vec<Assertion> {
        let mut wfs = Vec::new();
        let all_vars: Vec<_> = self.all_vars().collect();
        for (nm, ty) in all_vars {
            let lvar = Expr::LVar(format!("#{nm}"));
            wfs.push(make_wf_asrt(ctx, self.temp_gen, lvar, ty));
        }

        wfs
    }

    /// Asserts that inputs equal their respective lvars.
    pub fn store_eq_var(&self) -> Vec<Assertion> {
        let mut wfs = Vec::new();

        for (nm, _) in self.all_vars() {
            let lvar = Expr::LVar(format!("#{nm}"));
            wfs.push(Expr::PVar(nm.to_string()).eq_f(lvar).into_asrt());
        }
        wfs
    }

    /// Asserts that inputs equal their respective lvars.
    pub fn store_eq_all(&self) -> Vec<Assertion> {
        let mut wfs = Vec::new();

        for arg in self.physical_args() {
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
    /// Panics if the postcondition contains a disjunction
    pub fn user_post(&mut self) -> Option<Assertion> {
        let contract = self.contract.as_ref()?;
        assert_eq!(contract.post.len(), 1);
        let subst: HashMap<_, _> = contract.post[0]
            .0
            .iter()
            .map(|lvar| (lvar.0.to_string(), Expr::LVar(self.temp_gen.fresh_lvar())))
            .collect();
        let mut post = contract.post[0].1.clone();

        post.subst_lvar(&subst);
        Some(post)
    }

    /// Returns a precondition elaborated with well-formedness and mutable-store assertions
    /// and a boolean that says if this contract is trusted
    fn full_pre(&mut self, ctx: &mut GlobalEnv<'tcx>) -> Option<(Assertion, bool)> {
        let mut wf = self.type_wf_pres(ctx);
        let lv = self.store_eq_all();
        let contract = self.contract.as_ref()?;
        let mut pre = contract.pre.clone();

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

        if !contract.timeless {
            for lft in self.lifetimes() {
                let lvar = Expr::LVar(format!("#{lft}"));
                wf.push(crate::logic::core_preds::alive_lft(lvar));
            }
        }
        let full_pre = lv.into_iter().chain(wf).rfold(pre, Assertion::star);

        Some((full_pre, contract.trusted))
    }

    fn full_post(&self) -> Vec<Assertion> {
        let mut wf = Vec::new();
        let timeless = match self.contract.as_ref() {
            None => false,
            Some(c) => c.timeless,
        };
        if !timeless {
            for lft in self.lifetimes() {
                let lvar = Expr::LVar(format!("#{lft}"));
                wf.push(crate::logic::core_preds::alive_lft(lvar));
            }
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

        let mut post = self
            .contract
            .as_ref()
            .map(|c| c.post.clone())
            .unwrap_or_default();
        post.iter_mut().for_each(|p| p.1.subst_pvar(&var_map));

        post.into_iter()
            .map(|(_, post)| wf.clone().into_iter().rfold(post, Assertion::star))
            .collect()
    }

    /// Return a gil spec for a procedure corresponding to this signature
    pub fn into_gil_spec(mut self, ctx: &mut GlobalEnv<'tcx>, name: String) -> Option<Spec> {
        let (pre, trusted) = self.full_pre(ctx)?;

        let sspec = SingleSpec {
            pre,
            posts: self.full_post(),
            flag: Flag::Normal,
            trusted,
        };
        Some(Spec {
            params: self.physical_args().map(|a| a.name().to_string()).collect(),
            name,
            sspecs: vec![sspec],
        })
    }
}

pub fn build_signature<'tcx, 'genv>(
    global_env: &mut GlobalEnv<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    temp_gen: &'genv mut TempGenerator,
) -> Signature<'tcx, 'genv> {
    assert!(
        matches!(
            global_env.tcx().def_kind(id),
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure
        ),
        "Cannot build signature for {:?}",
        global_env.tcx().def_kind(id)
    );
    let tcx = global_env.tcx();

    // TODO: Fix, this is wrong in a context where we are building a substitution for an (id, subst) pair, consider
    // the case of a function `fn<T>(..)` where we apply `T = (U, V)`, we should build something which looks more like `fn<U,V>`.
    // This means I don't think we want to use the generics at all?

    let mut args = Vec::new();
    let (inputs, output) = inputs_and_output(tcx, id);
    let mut inputs: Vec<_> = EarlyBinder::bind(inputs.collect()).instantiate(tcx, subst);
    let output = EarlyBinder::bind(output).instantiate(tcx, subst);
    // A "magic closure" is a closure used to define a gillian-rust item. In this case we drop the closure environment as a parameter since it's "fake".
    let magic_closure = is_magic_closure(id, tcx);

    if args_deferred(id, tcx) {
        let spec_id = global_env.specification_id(id);
        let (spec_inputs, _) = inputs_and_output(tcx, spec_id.unwrap());
        inputs = spec_inputs.skip(1).collect();
    }

    let inputs = if magic_closure {
        inputs[1..].to_vec()
    } else {
        inputs.clone()
    };

    // let sig = tcx.fn_sig(id).instantiate(tcx, subst);
    let substsref = subst;

    let mut regions = collect_regions(inputs.clone()).regions;
    regions.extend(collect_regions(output).regions);
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
        }
    }

    let params: IndexSet<_> = collect_params(inputs.clone())
        .chain(collect_params(output))
        .collect();

    for pty in params {
        let arg = ParamKind::Generic(Symbol::intern(&type_param_name(pty.index, pty.name)));

        args.push(arg)
    }

    let mut subst = HashMap::new();

    for (idx, (ident, ty)) in inputs.into_iter().enumerate() {
        let prog_name = if ident.name.as_str().is_empty() {
            anonymous_param_symbol(idx)
        } else {
            ident.name
        };
        args.push(ParamKind::Program(prog_name, ty));
        subst.insert(prog_name.to_string(), Expr::PVar(prog_name.to_string()));
    }

    let (uni_vars, contract) = if let Some(spec_id) = global_env.specification_id(id) {
        let (uni, mut pre, mut post, trusted) =
            PredCtx::new_with_args(global_env, temp_gen, spec_id, substsref).raw_spec();

        if !(is_lemma(id, tcx) || is_predicate(id, tcx)) {
            pre.subst_pvar(&subst);
            post.iter_mut()
                .for_each(|(_, post)| post.subst_pvar(&subst));
        }

        let timeless = crate::utils::attrs::is_timeless(id, tcx);

        (
            uni,
            Some(Contract {
                pre,
                post,
                trusted,
                timeless,
            }),
        )
    } else {
        (Default::default(), None)
    };

    args.extend(
        uni_vars
            .into_iter()
            .map(|(nm, ty)| ParamKind::Logic(nm, ty)),
    );

    Signature {
        args,
        contract,
        temp_gen,
    }
}

pub(crate) fn anonymous_param_symbol(idx: usize) -> Symbol {
    Symbol::intern(&format!("G_{}", idx + 1))
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

pub fn make_wf_asrt<'tcx>(
    ctx: &mut GlobalEnv<'tcx>,
    temps: &mut TempGenerator,
    e: Expr,
    ty: Ty<'tcx>,
) -> Assertion {
    // The type here is already substituted
    if let Some(inner_ty) = ty_utils::peel_mut_ref(ty) {
        if ctx.config.prophecies {
            let sized = !(inner_ty.is_slice() || inner_ty.is_str());
            return make_is_mut_ref_proph_asrt(temps, e, sized);
        }
    }
    if let Some(inner_ty) = ty_utils::peel_any_ptr(ty) {
        let sized = !(inner_ty.is_slice() || inner_ty.is_str());
        make_is_ptr_asrt(temps, e, sized)
    } else if ty.is_integral() {
        Assertion::Types(vec![(e, Type::IntType)])
    } else if let Some(inner_ty) = ty_utils::peel_nonnull(ty, ctx.tcx()) {
        let sized = !(inner_ty.is_slice() || inner_ty.is_str());
        make_is_nonnull_asrt(temps, e, sized)
    } else if let Some(inner_ty) = ty_utils::peel_unique(ty, ctx.tcx()) {
        let sized = !(inner_ty.is_slice() || inner_ty.is_str());
        make_is_unique_asrt(temps, e, sized)
    } else if crate::utils::ty::is_unsigned_integral(ty) {
        Formula::i_le(0, e).into_asrt()
    } else {
        Assertion::Emp
    }
}

// fn make_nonnull<'tcx>(tcx: TyCtxt<'tcx>, ptr: Expr) -> Expr {
//     [ptr].into()
// }

fn make_is_ptr_asrt(fresh: &mut TempGenerator, e: Expr, sized: bool) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    if sized {
        types.star(e.eq_f([loc, proj]).into_asrt())
    } else {
        let len = temp_lvar(fresh);
        let len_type = Assertion::Types(vec![(len.clone(), Type::IntType)]);
        types
            .star(len_type)
            .star(e.eq_f([[loc, proj].into(), len]).into_asrt())
    }
}

fn make_is_nonnull_asrt(fresh: &mut TempGenerator, e: Expr, sized: bool) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    if sized {
        let ptr = Expr::EList(vec![loc, proj]);
        types.star(e.eq_f([ptr]).into_asrt())
    } else {
        let len = temp_lvar(fresh);
        let len_type = Assertion::Types(vec![(len.clone(), Type::IntType)]);
        let ptr = Expr::EList(vec![[loc, proj].into(), len]);
        types.star(len_type).star(e.eq_f([ptr]).into_asrt())
    }
}

fn make_is_unique_asrt(fresh: &mut TempGenerator, e: Expr, sized: bool) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
    ]);
    if sized {
        let ptr: Expr = [loc, proj].into();
        let nonnull: Expr = [ptr].into();
        let unique: Expr = [nonnull, vec![].into()].into();
        types.star(e.eq_f(unique).into_asrt())
    } else {
        let len = temp_lvar(fresh);
        let len_type = Assertion::Types(vec![(len.clone(), Type::IntType)]);
        let ptr = Expr::EList(vec![[loc, proj].into(), len]);
        let nonnull: Expr = [ptr].into();
        let unique: Expr = [nonnull, vec![].into()].into();
        types.star(len_type).star(e.eq_f(unique).into_asrt())
    }
}

fn make_is_mut_ref_proph_asrt(fresh: &mut TempGenerator, e: Expr, sized: bool) -> Assertion {
    let loc = temp_lvar(fresh);
    let proj = temp_lvar(fresh);
    let pcy = temp_lvar(fresh);
    let types = Assertion::Types(vec![
        (loc.clone(), Type::ObjectType),
        (proj.clone(), Type::ListType),
        (pcy.clone(), Type::ObjectType),
    ]);
    if sized {
        types.star(e.eq_f([[loc, proj].into(), pcy]).into_asrt())
    } else {
        let len = temp_lvar(fresh);
        let len_type = Assertion::Types(vec![(len.clone(), Type::IntType)]);
        types
            .star(len_type)
            .star(e.eq_f([[[loc, proj].into(), len].into(), pcy]).into_asrt())
    }
}

fn temp_lvar(fresh: &mut TempGenerator) -> Expr {
    Expr::LVar(fresh.fresh_lvar())
}

pub(crate) fn inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (impl Iterator<Item = (symbol::Ident, Ty<'tcx>)>, Ty<'tcx>) {
    let ty = tcx.type_of(def_id).instantiate_identity();
    let (inputs, output): (Box<dyn Iterator<Item = (rustc_span::symbol::Ident, _)>>, _) = match ty
        .kind()
    {
        TyKind::FnDef(..) => {
            let gen_sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = gen_sig.skip_binder();
            let iter = tcx
                .fn_arg_names(def_id)
                .iter()
                .cloned()
                .zip(sig.inputs().iter().cloned());
            (Box::new(iter), sig.output())
        }
        TyKind::Closure(_, subst) => {
            let sig = tcx.signature_unclosure(subst.as_closure().sig(), Unsafety::Normal);
            let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), sig);
            let env_ty = tcx.closure_env_ty(ty, subst.as_closure().kind(), tcx.lifetimes.re_erased);

            // I wish this could be called "self"
            let closure_env = (symbol::Ident::empty(), env_ty);
            let names = tcx
                .fn_arg_names(def_id)
                .iter()
                .cloned()
                .chain(iter::repeat(rustc_span::symbol::Ident::empty()));
            (
                Box::new(iter::once(closure_env).chain(names.zip(sig.inputs().iter().cloned()))),
                sig.output(),
            )
        }
        _ => (
            Box::new(iter::empty()),
            tcx.type_of(def_id).instantiate_identity(),
        ),
    };
    (inputs, output)
}

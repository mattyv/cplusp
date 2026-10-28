//! The translator: globals, decision 0173. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ globals, decision 0173

/// The scalar of a global that can be a reference parameter of 0108. A global of any other type has no rule yet.
pub open spec fn spec_global_scalar(t: Ty) -> Option<Scalar> {
    match t {
        Ty::I32 => Some(Scalar::I32),
        Ty::I64 => Some(Scalar::I64),
        Ty::U8 => Some(Scalar::U8),
        Ty::U32 => Some(Scalar::U32),
        Ty::U64 => Some(Scalar::U64),
        Ty::Bool => Some(Scalar::Bool),
        Ty::Struct(k) => Some(Scalar::Struct(k)),
        _ => None,
    }
}

pub fn global_scalar(t: Ty) -> (r: Option<Scalar>)
    ensures
        r == spec_global_scalar(t),
{
    match t {
        Ty::I32 => Some(Scalar::I32),
        Ty::I64 => Some(Scalar::I64),
        Ty::U8 => Some(Scalar::U8),
        Ty::U32 => Some(Scalar::U32),
        Ty::U64 => Some(Scalar::U64),
        Ty::Bool => Some(Scalar::Bool),
        Ty::Struct(k) => Some(Scalar::Struct(k)),
        _ => None,
    }
}

/// A line of the kind `k` names the global `g`.
pub open spec fn spec_glists(cs: Conds, k: CondKind, g: u32) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k2, e, _, _), rest) => (k2 == k && e == Expr::Name(g)) || spec_glists(*rest, k, g),
    }
}

pub fn glists(cs: &Conds, k: CondKind, g: u32) -> (r: bool)
    ensures
        r == spec_glists(*cs, k, g),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k2, e, _, _), rest) => (*k2 == k && match e {
            Expr::Name(n) => *n == g,
            _ => false,
        }) || glists(rest, k, g),
    }
}

/// The line of the first modifies or reads line that names the global `g`.
pub open spec fn spec_gline(cs: Conds, g: u32) -> Option<u32>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, _), rest) => if (k == CondKind::Modifies || k == CondKind::Reads) && e == Expr::Name(g) {
            Some(l)
        } else {
            spec_gline(*rest, g)
        },
    }
}

pub fn gline(cs: &Conds, g: u32) -> (r: Option<u32>)
    ensures
        r == spec_gline(*cs, g),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, _), rest) => if (*k == CondKind::Modifies || *k == CondKind::Reads) && match e {
            Expr::Name(n) => *n == g,
            _ => false,
        } {
            Some(*l)
        } else {
            gline(rest, g)
        },
    }
}

/// The globals that a function lists, as its implicit parameters, in the order of the globals `gs`. A global on a modifies line is
/// a reference parameter, and one on a reads line only is a parameter by value, decision 0173.
pub open spec fn spec_gparams(cs: Conds, gs: Params) -> Params
    decreases gs,
{
    match gs {
        List::Nil => List::Nil,
        List::Cons((g, t), rest) => if spec_glists(cs, CondKind::Modifies, g) {
            match spec_global_scalar(t) {
                Some(s) => List::Cons((g, Ty::Mut(s)), Box::new(spec_gparams(cs, *rest))),
                None => spec_gparams(cs, *rest),
            }
        } else if spec_glists(cs, CondKind::Reads, g) && spec_global_scalar(t) is Some {
            List::Cons((g, t), Box::new(spec_gparams(cs, *rest)))
        } else {
            spec_gparams(cs, *rest)
        },
    }
}

pub fn gparams(cs: &Conds, gs: &Params) -> (r: Params)
    ensures
        r == spec_gparams(*cs, *gs),
    decreases gs,
{
    match gs {
        List::Nil => List::Nil,
        List::Cons((g, t), rest) => if glists(cs, CondKind::Modifies, *g) {
            match global_scalar(*t) {
                Some(s) => List::Cons((*g, Ty::Mut(s)), Box::new(gparams(cs, rest))),
                None => gparams(cs, rest),
            }
        } else if glists(cs, CondKind::Reads, *g) && global_scalar(*t).is_some() {
            List::Cons((*g, *t), Box::new(gparams(cs, rest)))
        } else {
            gparams(cs, rest)
        },
    }
}

/// A use of the name `v` of type `t`. A name that a parameter, a local or a parameter of a lambda hides stays. A global that the
/// function lists has the type of its implicit parameter. A global that the function does not list names nothing, so it is refused
/// as a name. Any other name stays.
pub open spec fn spec_gvar(v: u32, t: Ty, gs: Params, gps: Params, hide: Names) -> Expr {
    if spec_has(hide, v) {
        Expr::Var(v, t)
    } else {
        match spec_get(gps, v) {
            Some(t2) => Expr::Var(v, t2),
            None => if spec_get(gs, v) is Some {
                Expr::Name(v)
            } else {
                Expr::Var(v, t)
            },
        }
    }
}

pub fn gvar(v: u32, t: Ty, gs: &Params, gps: &Params, hide: &Names) -> (r: Expr)
    ensures
        r == spec_gvar(v, t, *gs, *gps, *hide),
{
    if has(hide, v) {
        Expr::Var(v, t)
    } else {
        match get(gps, v) {
            Some(t2) => Expr::Var(v, t2),
            None => if get(gs, v).is_some() {
                Expr::Name(v)
            } else {
                Expr::Var(v, t)
            },
        }
    }
}

/// The arguments that a call adds for the globals `cps` of its callee: the parameter of the caller of each name, or the name alone,
/// which is refused, when the caller lists no such global.
pub open spec fn spec_gpass(cps: Params, gps: Params) -> Args
    decreases cps,
{
    match cps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(Box::new(match spec_get(gps, g) {
            Some(t2) => Expr::Var(g, t2),
            None => Expr::Name(g),
        }), Box::new(spec_gpass(*rest, gps))),
    }
}

pub fn gpass(cps: &Params, gps: &Params) -> (r: Args)
    ensures
        r == spec_gpass(*cps, *gps),
    decreases cps,
{
    match cps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(Box::new(match get(gps, *g) {
            Some(t2) => Expr::Var(*g, t2),
            None => Expr::Name(*g),
        }), Box::new(gpass(rest, gps))),
    }
}

/// The arguments of the globals of the callee `k`.
pub open spec fn spec_gextra(k: u32, gs: Params, gps: Params, fs: Fns) -> Args {
    match spec_find(fs, k) {
        Some(cf) => spec_gpass(spec_gparams(cf.conds, gs), gps),
        None => List::Nil,
    }
}

pub fn gextra(k: u32, gs: &Params, gps: &Params, fs: &Fns) -> (r: Args)
    ensures
        r == spec_gextra(k, *gs, *gps, *fs),
{
    match find(fs, k) {
        Some(cf) => gpass(&gparams(&cf.conds, gs), gps),
        None => List::Nil,
    }
}

/// An expression of code with each global typed by the implicit parameters `gps`, and each call given the globals of its callee.
pub open spec fn spec_gexpr(e: Expr, gs: Params, gps: Params, hide: Names, fs: Fns) -> Expr
    decreases e,
{
    match e {
        Expr::Int(f0) => Expr::Int(f0),
        Expr::Lit(f0, f1) => Expr::Lit(f0, f1),
        Expr::Bool(f0) => Expr::Bool(f0),
        Expr::Var(v, t) => spec_gvar(v, t, gs, gps, hide),
        Expr::Name(f0) => Expr::Name(f0),
        Expr::Result => Expr::Result,
        Expr::Bin(f0, f1, f2) => Expr::Bin(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Not(f0) => Expr::Not(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Neg(f0) => Expr::Neg(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Cast(f0, f1) => Expr::Cast(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Paren(f0) => Expr::Paren(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Brace(f0) => Expr::Brace(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Call(k, nm, args, at) => Expr::Call(k, nm, Box::new(spec_append(spec_gargs(*args, gs, gps, hide, fs), spec_gextra(k, gs, gps, fs))), at),
        Expr::Size(f0) => Expr::Size(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Back(f0) => Expr::Back(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Index(f0, f1) => Expr::Index(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Copy(f0, f1, f2) => Expr::Copy(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, f2),
        Expr::Field(f0, f1) => Expr::Field(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1),
        Expr::Construct(f0, f1) => Expr::Construct(f0, Box::new(spec_gargs(*f1, gs, gps, hide, fs))),
        Expr::Forall(f0, f1) => Expr::Forall(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Exists(f0, f1) => Expr::Exists(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Chain(f0, f1, f2, f3, f4) => Expr::Chain(f0, f1, Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), Box::new(spec_gexpr(*f3, gs, gps, hide, fs)), Box::new(spec_gexpr(*f4, gs, gps, hide, fs))),
        Expr::HasValue(f0) => Expr::HasValue(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Value(f0) => Expr::Value(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Nullopt => Expr::Nullopt,
        Expr::Wrap(f0) => Expr::Wrap(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Empty(f0) => Expr::Empty(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Subspan(f0, f1) => Expr::Subspan(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Apply(f0, f1) => Expr::Apply(f0, Box::new(spec_gargs(*f1, gs, gps, hide, fs))),
        Expr::Suffix(f0, f1) => Expr::Suffix(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Prefix(f0, f1) => Expr::Prefix(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Slice(f0, f1, f2) => Expr::Slice(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Divide(f0, f1, f2, f3) => Expr::Divide(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), f3),
        Expr::MApply(f0, f1, f2) => Expr::MApply(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, Box::new(spec_gargs(*f2, gs, gps, hide, fs))),
        Expr::Old(f0) => Expr::Old(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Cond(f0, f1, f2) => Expr::Cond(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Shr(f0, f1, f2) => Expr::Shr(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), f2),
        Expr::Bits(f0, f1, f2, f3) => Expr::Bits(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), f3),
        Expr::StaticCast(f0, f1) => Expr::StaticCast(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::List(f0) => Expr::List(Box::new(spec_gargs(*f0, gs, gps, hide, fs))),
        // A write of a global writes the parameter that it becomes, decision 0177.
        Expr::Step(f0, f1, f2, f3) => match spec_gvar(f0, f1, gs, gps, hide) {
            Expr::Var(v, t) => Expr::Step(v, t, f2, f3),
            other => other,
        },
        Expr::Enumerator(f0, f1) => Expr::Enumerator(f0, f1),
        // The parameter of the lambda hides a global of its name in the body, as in C++.
        Expr::CountIf(f0, f1, f2, f3) => Expr::CountIf(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, f2, Box::new(spec_gexpr(*f3, gs, gps, List::Cons(f1, Box::new(hide)), fs))),
        Expr::RealLit(f0, f1) => Expr::RealLit(f0, f1),
        Expr::Ratio(f0, f1) => Expr::Ratio(f0, f1),
        Expr::Finite(f0) => Expr::Finite(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Abs(f0) => Expr::Abs(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Eps => Expr::Eps,
        Expr::Eta => Expr::Eta,
        Expr::DblMax => Expr::DblMax,
        Expr::EmptyVec => Expr::EmptyVec,
        Expr::Fill(f0, f1) => Expr::Fill(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Move(f0, f1) => Expr::Move(f0, f1),
        Expr::Unknown(f0, f1) => Expr::Unknown(f0, f1),
    }
}

pub open spec fn spec_gargs(args: Args, gs: Params, gps: Params, hide: Names, fs: Fns) -> Args
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => List::Cons(Box::new(spec_gexpr(*a, gs, gps, hide, fs)), Box::new(spec_gargs(*rest, gs, gps, hide, fs))),
    }
}

pub fn gexpr(e: &Expr, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Expr)
    ensures
        r == spec_gexpr(*e, *gs, *gps, *hide, *fs),
    decreases e,
{
    match e {
        Expr::Int(f0) => Expr::Int(*f0),
        Expr::Lit(f0, f1) => Expr::Lit(*f0, *f1),
        Expr::Bool(f0) => Expr::Bool(*f0),
        Expr::Var(v, t) => gvar(*v, *t, gs, gps, hide),
        Expr::Name(f0) => Expr::Name(*f0),
        Expr::Result => Expr::Result,
        Expr::Bin(f0, f1, f2) => Expr::Bin(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Not(f0) => Expr::Not(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Neg(f0) => Expr::Neg(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Cast(f0, f1) => Expr::Cast(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Paren(f0) => Expr::Paren(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Brace(f0) => Expr::Brace(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Call(k, nm, args, at) => Expr::Call(*k, *nm, Box::new(append(gargs(args, gs, gps, hide, fs), gextra(*k, gs, gps, fs))), *at),
        Expr::Size(f0) => Expr::Size(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Back(f0) => Expr::Back(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Index(f0, f1) => Expr::Index(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Copy(f0, f1, f2) => Expr::Copy(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, *f2),
        Expr::Field(f0, f1) => Expr::Field(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1),
        Expr::Construct(f0, f1) => Expr::Construct(*f0, Box::new(gargs(f1, gs, gps, hide, fs))),
        Expr::Forall(f0, f1) => Expr::Forall(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Exists(f0, f1) => Expr::Exists(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Chain(f0, f1, f2, f3, f4) => Expr::Chain(*f0, *f1, Box::new(gexpr(f2, gs, gps, hide, fs)), Box::new(gexpr(f3, gs, gps, hide, fs)), Box::new(gexpr(f4, gs, gps, hide, fs))),
        Expr::HasValue(f0) => Expr::HasValue(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Value(f0) => Expr::Value(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Nullopt => Expr::Nullopt,
        Expr::Wrap(f0) => Expr::Wrap(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Empty(f0) => Expr::Empty(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Subspan(f0, f1) => Expr::Subspan(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Apply(f0, f1) => Expr::Apply(*f0, Box::new(gargs(f1, gs, gps, hide, fs))),
        Expr::Suffix(f0, f1) => Expr::Suffix(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Prefix(f0, f1) => Expr::Prefix(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Slice(f0, f1, f2) => Expr::Slice(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Divide(f0, f1, f2, f3) => Expr::Divide(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs)), *f3),
        Expr::MApply(f0, f1, f2) => Expr::MApply(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, Box::new(gargs(f2, gs, gps, hide, fs))),
        Expr::Old(f0) => Expr::Old(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Cond(f0, f1, f2) => Expr::Cond(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Shr(f0, f1, f2) => Expr::Shr(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), *f2),
        Expr::Bits(f0, f1, f2, f3) => Expr::Bits(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs)), *f3),
        Expr::StaticCast(f0, f1) => Expr::StaticCast(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::List(f0) => Expr::List(Box::new(gargs(f0, gs, gps, hide, fs))),
        Expr::Step(f0, f1, f2, f3) => match gvar(*f0, *f1, gs, gps, hide) {
            Expr::Var(v, t) => Expr::Step(v, t, *f2, *f3),
            other => other,
        },
        Expr::Enumerator(f0, f1) => Expr::Enumerator(*f0, *f1),
        Expr::CountIf(f0, f1, f2, f3) => Expr::CountIf(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, *f2, Box::new(gexpr(f3, gs, gps, &List::Cons(*f1, Box::new(copy(hide))), fs))),
        Expr::RealLit(f0, f1) => Expr::RealLit(*f0, *f1),
        Expr::Ratio(f0, f1) => Expr::Ratio(*f0, *f1),
        Expr::Finite(f0) => Expr::Finite(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Abs(f0) => Expr::Abs(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Eps => Expr::Eps,
        Expr::Eta => Expr::Eta,
        Expr::DblMax => Expr::DblMax,
        Expr::EmptyVec => Expr::EmptyVec,
        Expr::Fill(f0, f1) => Expr::Fill(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Move(f0, f1) => Expr::Move(*f0, *f1),
        Expr::Unknown(f0, f1) => Expr::Unknown(*f0, *f1),
    }
}

pub fn gargs(args: &Args, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Args)
    ensures
        r == spec_gargs(*args, *gs, *gps, *hide, *fs),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => List::Cons(Box::new(gexpr(a, gs, gps, hide, fs)), Box::new(gargs(rest, gs, gps, hide, fs))),
    }
}

/// The calls of an expression, as the key, the id of the name and the line of each.
pub open spec fn spec_gcalls(e: Expr) -> List<(u32, u32, u32)>
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::Not(f0) => spec_gcalls(*f0),
        Expr::Neg(f0) => spec_gcalls(*f0),
        Expr::Cast(_, f1) => spec_gcalls(*f1),
        Expr::Paren(f0) => spec_gcalls(*f0),
        Expr::Brace(f0) => spec_gcalls(*f0),
        Expr::Call(k, nm, args, at) => List::Cons((k, nm, at), Box::new(spec_gcalls_args(*args))),
        Expr::Size(f0) => spec_gcalls(*f0),
        Expr::Back(f0) => spec_gcalls(*f0),
        Expr::Index(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Copy(f0, _, _) => spec_gcalls(*f0),
        Expr::Field(f0, _) => spec_gcalls(*f0),
        Expr::Construct(_, f1) => spec_gcalls_args(*f1),
        Expr::Forall(_, f1) => spec_gcalls(*f1),
        Expr::Exists(_, f1) => spec_gcalls(*f1),
        Expr::Chain(_, _, f2, f3, f4) => spec_append(spec_gcalls(*f2), spec_append(spec_gcalls(*f3), spec_gcalls(*f4))),
        Expr::HasValue(f0) => spec_gcalls(*f0),
        Expr::Value(f0) => spec_gcalls(*f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => spec_gcalls(*f0),
        Expr::Empty(f0) => spec_gcalls(*f0),
        Expr::Subspan(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Apply(_, f1) => spec_gcalls_args(*f1),
        Expr::Suffix(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Prefix(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Slice(f0, f1, f2) => spec_append(spec_gcalls(*f0), spec_append(spec_gcalls(*f1), spec_gcalls(*f2))),
        Expr::Divide(_, f1, f2, _) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::MApply(f0, _, f2) => spec_append(spec_gcalls(*f0), spec_gcalls_args(*f2)),
        Expr::Old(f0) => spec_gcalls(*f0),
        Expr::Cond(f0, f1, f2) => spec_append(spec_gcalls(*f0), spec_append(spec_gcalls(*f1), spec_gcalls(*f2))),
        Expr::Shr(f0, f1, _) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Bits(_, f1, f2, _) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::StaticCast(_, f1) => spec_gcalls(*f1),
        Expr::List(f0) => spec_gcalls_args(*f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => spec_append(spec_gcalls(*f0), spec_gcalls(*f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => spec_gcalls(*f0),
        Expr::Abs(f0) => spec_gcalls(*f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub open spec fn spec_gcalls_args(args: Args) -> List<(u32, u32, u32)>
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_gcalls(*a), spec_gcalls_args(*rest)),
    }
}

pub fn gcalls(e: &Expr) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls(*e),
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => append(gcalls(f1), gcalls(f2)),
        Expr::Not(f0) => gcalls(f0),
        Expr::Neg(f0) => gcalls(f0),
        Expr::Cast(_, f1) => gcalls(f1),
        Expr::Paren(f0) => gcalls(f0),
        Expr::Brace(f0) => gcalls(f0),
        Expr::Call(k, nm, args, at) => List::Cons((*k, *nm, *at), Box::new(gcalls_args(args))),
        Expr::Size(f0) => gcalls(f0),
        Expr::Back(f0) => gcalls(f0),
        Expr::Index(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Copy(f0, _, _) => gcalls(f0),
        Expr::Field(f0, _) => gcalls(f0),
        Expr::Construct(_, f1) => gcalls_args(f1),
        Expr::Forall(_, f1) => gcalls(f1),
        Expr::Exists(_, f1) => gcalls(f1),
        Expr::Chain(_, _, f2, f3, f4) => append(gcalls(f2), append(gcalls(f3), gcalls(f4))),
        Expr::HasValue(f0) => gcalls(f0),
        Expr::Value(f0) => gcalls(f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => gcalls(f0),
        Expr::Empty(f0) => gcalls(f0),
        Expr::Subspan(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Apply(_, f1) => gcalls_args(f1),
        Expr::Suffix(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Prefix(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Slice(f0, f1, f2) => append(gcalls(f0), append(gcalls(f1), gcalls(f2))),
        Expr::Divide(_, f1, f2, _) => append(gcalls(f1), gcalls(f2)),
        Expr::MApply(f0, _, f2) => append(gcalls(f0), gcalls_args(f2)),
        Expr::Old(f0) => gcalls(f0),
        Expr::Cond(f0, f1, f2) => append(gcalls(f0), append(gcalls(f1), gcalls(f2))),
        Expr::Shr(f0, f1, _) => append(gcalls(f0), gcalls(f1)),
        Expr::Bits(_, f1, f2, _) => append(gcalls(f1), gcalls(f2)),
        Expr::StaticCast(_, f1) => gcalls(f1),
        Expr::List(f0) => gcalls_args(f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => append(gcalls(f0), gcalls(f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => gcalls(f0),
        Expr::Abs(f0) => gcalls(f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub fn gcalls_args(args: &Args) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(gcalls(a), gcalls_args(rest)),
    }
}

/// A write to the name `n` that is a global the function neither lists nor hides. It names nothing, so the pass refuses the name.
pub open spec fn spec_gwrite_bad(n: u32, gs: Params, gps: Params, hide: Names) -> bool {
    spec_get(gps, n) is None && spec_get(gs, n) is Some && !spec_has(hide, n)
}

pub fn gwrite_bad(n: u32, gs: &Params, gps: &Params, hide: &Names) -> (r: bool)
    ensures
        r == spec_gwrite_bad(n, *gs, *gps, *hide),
{
    get(gps, n).is_none() && get(gs, n).is_some() && !(has(hide, n))
}

/// A statement of the body with each global typed by the implicit parameters and each call given the globals of its callee. The
/// lines of a loop and the lines of an assert or apply are contract lines, which read a global by its name, so they stay.
pub open spec fn spec_gstmt(s: Stmt, gs: Params, gps: Params, hide: Names, fs: Fns) -> Stmt
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::If(c, t, f, l) => Stmt::If(spec_gexpr(c, gs, gps, hide, fs), Box::new(spec_gstmts(*t, gs, gps, hide, fs)), Box::new(spec_gstmts(*f, gs, gps, hide, fs)), l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(spec_gstmts(*b, gs, gps, hide, fs)), l),
        Stmt::Local(n, t, e, l) => Stmt::Local(n, t, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::Assign(n, e, l) => if spec_gwrite_bad(n, gs, gps, hide) {
            Stmt::Assign(n, Expr::Name(n), l)
        } else {
            Stmt::Assign(n, spec_gexpr(e, gs, gps, hide, fs), l)
        },
        Stmt::Step(n, t, up, l) => if spec_gwrite_bad(n, gs, gps, hide) {
            Stmt::Assign(n, Expr::Name(n), l)
        } else {
            Stmt::Step(n, t, up, l)
        },
        Stmt::While(c, lc, body, l) => Stmt::While(spec_gexpr(c, gs, gps, hide, fs), lc, Box::new(spec_gstmts(*body, gs, gps, hide, fs)), l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(spec_gstmt(*init, gs, gps, hide, fs)),
            spec_gexpr(c, gs, gps, hide, fs),
            Box::new(spec_gstmt(*step, gs, gps, hide, fs)),
            lc,
            Box::new(spec_gstmts(*body, gs, gps, hide, fs)),
            l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(x, f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(x, f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(spec_gexpr(e, gs, gps, hide, fs), k, Box::new(spec_gcases(*cs, gs, gps, hide, fs)), l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(k, nm, Box::new(spec_append(spec_gargs(*args, gs, gps, hide, fs), spec_gextra(k, gs, gps, fs))), l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(fr, x, xt, spec_gexpr(sq, gs, gps, hide, fs), lc, Box::new(spec_gstmts(*body, gs, gps, hide, fs)), l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(v, spec_gexpr(i, gs, gps, hide, fs), spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(f, spec_gexpr(i, gs, gps, hide, fs), spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::PushField(f, e, l) => Stmt::PushField(f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetThroughField(f, g, e, l) => Stmt::SetThroughField(f, g, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(v, spec_gexpr(e, gs, gps, hide, fs), l),
        // The comparator reads a listed global as the function does. Its two parameters hide globals of their names.
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(v, a, b, t, spec_gexpr(e, gs, gps, List::Cons(a, Box::new(List::Cons(b, Box::new(hide)))), fs), l),
        _ => s,
    }
}

pub open spec fn spec_gstmts(ss: Stmts, gs: Params, gps: Params, hide: Names, fs: Fns) -> Stmts
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(spec_gstmt(*s, gs, gps, hide, fs)), Box::new(spec_gstmts(*rest, gs, gps, hide, fs))),
    }
}

pub open spec fn spec_gcases(cs: Cases, gs: Params, gps: Params, hide: Names, fs: Fns) -> Cases
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((i, Box::new(spec_gstmts(*body, gs, gps, hide, fs))), Box::new(spec_gcases(*rest, gs, gps, hide, fs))),
    }
}

pub fn copy_conds(cs: &Conds) -> (r: Conds)
    ensures
        r == *cs,
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, d), rest) => List::Cons((*k, copy_expr(e), *l, copy(d)), Box::new(copy_conds(rest))),
    }
}

pub fn copy_stmt(s: &Stmt) -> (r: Stmt)
    ensures
        r == *s,
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(copy_expr(e), *l),
        Stmt::If(c, t, f, l) => Stmt::If(copy_expr(c), Box::new(copy_stmts(t)), Box::new(copy_stmts(f)), *l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(copy_stmts(b)), *l),
        Stmt::Local(n, t, e, l) => Stmt::Local(*n, *t, copy_expr(e), *l),
        Stmt::Assign(n, e, l) => Stmt::Assign(*n, copy_expr(e), *l),
        Stmt::Step(n, t, up, l) => Stmt::Step(*n, *t, *up, *l),
        Stmt::While(c, lc, body, l) => Stmt::While(copy_expr(c), Box::new(copy_conds(lc)), Box::new(copy_stmts(body)), *l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(copy_stmt(init)),
            copy_expr(c),
            Box::new(copy_stmt(step)),
            Box::new(copy_conds(lc)),
            Box::new(copy_stmts(body)),
            *l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(*f, copy_expr(e), *l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(*x, *f, copy_expr(e), *l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(*x, *f, copy_expr(e), *l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(copy_expr(e), *k, Box::new(copy_cases(cs)), *l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(*k, *nm, Box::new(copy_args(args)), *l),
        Stmt::Exit(l) => Stmt::Exit(*l),
        Stmt::Assert(e, l) => Stmt::Assert(copy_expr(e), *l),
        Stmt::Apply(k, args, l) => Stmt::Apply(*k, Box::new(copy_args(args)), *l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(*fr, *x, *xt, copy_expr(sq), Box::new(copy_conds(lc)), Box::new(copy_stmts(body)), *l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(*v, copy_expr(i), copy_expr(e), *l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(*f, copy_expr(i), copy_expr(e), *l),
        Stmt::PushField(f, e, l) => Stmt::PushField(*f, copy_expr(e), *l),
        Stmt::SetThroughField(f, g, e, l) => Stmt::SetThroughField(*f, *g, copy_expr(e), *l),
        Stmt::PopField(f, l) => Stmt::PopField(*f, *l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(*v, copy_expr(e), *l),
        Stmt::Sort(v, l) => Stmt::Sort(*v, *l),
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(*v, *a, *b, *t, copy_expr(e), *l),
        Stmt::Unknown(k, l) => Stmt::Unknown(*k, *l),
    }
}

pub fn copy_stmts(ss: &Stmts) -> (r: Stmts)
    ensures
        r == *ss,
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(copy_stmt(s)), Box::new(copy_stmts(rest))),
    }
}

pub fn copy_cases(cs: &Cases) -> (r: Cases)
    ensures
        r == *cs,
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((*i, Box::new(copy_stmts(body))), Box::new(copy_cases(rest))),
    }
}

pub fn gstmt(s: &Stmt, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Stmt)
    ensures
        r == spec_gstmt(*s, *gs, *gps, *hide, *fs),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(gexpr(e, gs, gps, hide, fs), *l),
        Stmt::If(c, t, f, l) => Stmt::If(gexpr(c, gs, gps, hide, fs), Box::new(gstmts(t, gs, gps, hide, fs)), Box::new(gstmts(f, gs, gps, hide, fs)), *l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(gstmts(b, gs, gps, hide, fs)), *l),
        Stmt::Local(n, t, e, l) => Stmt::Local(*n, *t, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::Assign(n, e, l) => if gwrite_bad(*n, gs, gps, hide) {
            Stmt::Assign(*n, Expr::Name(*n), *l)
        } else {
            Stmt::Assign(*n, gexpr(e, gs, gps, hide, fs), *l)
        },
        Stmt::Step(n, t, up, l) => if gwrite_bad(*n, gs, gps, hide) {
            Stmt::Assign(*n, Expr::Name(*n), *l)
        } else {
            Stmt::Step(*n, *t, *up, *l)
        },
        Stmt::While(c, lc, body, l) => Stmt::While(gexpr(c, gs, gps, hide, fs), Box::new(copy_conds(lc)), Box::new(gstmts(body, gs, gps, hide, fs)), *l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(gstmt(init, gs, gps, hide, fs)),
            gexpr(c, gs, gps, hide, fs),
            Box::new(gstmt(step, gs, gps, hide, fs)),
            Box::new(copy_conds(lc)),
            Box::new(gstmts(body, gs, gps, hide, fs)),
            *l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(*f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(*x, *f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(*x, *f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(gexpr(e, gs, gps, hide, fs), *k, Box::new(gcases(cs, gs, gps, hide, fs)), *l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(*k, *nm, Box::new(append(gargs(args, gs, gps, hide, fs), gextra(*k, gs, gps, fs))), *l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(*fr, *x, *xt, gexpr(sq, gs, gps, hide, fs), Box::new(copy_conds(lc)), Box::new(gstmts(body, gs, gps, hide, fs)), *l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(*v, gexpr(i, gs, gps, hide, fs), gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(*f, gexpr(i, gs, gps, hide, fs), gexpr(e, gs, gps, hide, fs), *l),
        Stmt::PushField(f, e, l) => Stmt::PushField(*f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetThroughField(f, g, e, l) => Stmt::SetThroughField(*f, *g, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(*v, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(*v, *a, *b, *t, gexpr(e, gs, gps, &List::Cons(*a, Box::new(List::Cons(*b, Box::new(copy(hide))))), fs), *l),
        _ => copy_stmt(s),
    }
}

pub fn gstmts(ss: &Stmts, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Stmts)
    ensures
        r == spec_gstmts(*ss, *gs, *gps, *hide, *fs),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(gstmt(s, gs, gps, hide, fs)), Box::new(gstmts(rest, gs, gps, hide, fs))),
    }
}

pub fn gcases(cs: &Cases, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Cases)
    ensures
        r == spec_gcases(*cs, *gs, *gps, *hide, *fs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((*i, Box::new(gstmts(body, gs, gps, hide, fs))), Box::new(gcases(rest, gs, gps, hide, fs))),
    }
}

/// The names of the locals of a body, at any depth, and the indexes and elements of its range-fors.
pub open spec fn spec_glocals(ss: Stmts) -> Names
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_glocals_stmt(*s), spec_glocals(*rest)),
    }
}

pub open spec fn spec_glocals_stmt(s: Stmt) -> Names
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, _) => List::Cons(n, Box::new(List::Nil)),
        Stmt::If(_, t, f, _) => spec_append(spec_glocals(*t), spec_glocals(*f)),
        Stmt::While(_, _, body, _) => spec_glocals(*body),
        Stmt::For(init, _, step, _, body, _) => spec_append(spec_glocals_stmt(*init), spec_append(spec_glocals_stmt(*step), spec_glocals(*body))),
        Stmt::Switch(_, _, cs, _) => spec_glocals_cases(*cs),
        Stmt::RangeFor(fr, x, _, _, _, body, _) => List::Cons(fr, Box::new(List::Cons(x, Box::new(spec_glocals(*body))))),
        _ => List::Nil,
    }
}

pub open spec fn spec_glocals_cases(cs: Cases) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_glocals(*body), spec_glocals_cases(*rest)),
    }
}

pub fn glocals(ss: &Stmts) -> (r: Names)
    ensures
        r == spec_glocals(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(glocals_stmt(s), glocals(rest)),
    }
}

pub fn glocals_stmt(s: &Stmt) -> (r: Names)
    ensures
        r == spec_glocals_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, _) => List::Cons(*n, Box::new(List::Nil)),
        Stmt::If(_, t, f, _) => append(glocals(t), glocals(f)),
        Stmt::While(_, _, body, _) => glocals(body),
        Stmt::For(init, _, step, _, body, _) => append(glocals_stmt(init), append(glocals_stmt(step), glocals(body))),
        Stmt::Switch(_, _, cs, _) => glocals_cases(cs),
        Stmt::RangeFor(fr, x, _, _, _, body, _) => List::Cons(*fr, Box::new(List::Cons(*x, Box::new(glocals(body))))),
        _ => List::Nil,
    }
}

pub fn glocals_cases(cs: &Cases) -> (r: Names)
    ensures
        r == spec_glocals_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(glocals(body), glocals_cases(rest)),
    }
}

/// The calls of a body, at any depth, as the key, the id of the name and the line of each.
pub open spec fn spec_gcalls_stmts(ss: Stmts) -> List<(u32, u32, u32)>
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_gcalls_stmt(*s), spec_gcalls_stmts(*rest)),
    }
}

pub open spec fn spec_gcalls_stmt(s: Stmt) -> List<(u32, u32, u32)>
    decreases s,
{
    match s {
        Stmt::Return(e, _) => spec_gcalls(e),
        Stmt::If(c, t, f, _) => spec_append(spec_gcalls(c), spec_append(spec_gcalls_stmts(*t), spec_gcalls_stmts(*f))),
        Stmt::Local(_, _, e, _) => spec_gcalls(e),
        Stmt::Assign(_, e, _) => spec_gcalls(e),
        Stmt::While(c, _, body, _) => spec_append(spec_gcalls(c), spec_gcalls_stmts(*body)),
        Stmt::For(init, c, step, _, body, _) => spec_append(spec_gcalls_stmt(*init), spec_append(spec_gcalls(c), spec_append(spec_gcalls_stmt(*step), spec_gcalls_stmts(*body)))),
        Stmt::SetField(_, e, _) => spec_gcalls(e),
        Stmt::SetRefField(_, _, e, _) => spec_gcalls(e),
        Stmt::SetOwnField(_, _, e, _) => spec_gcalls(e),
        Stmt::Switch(e, _, cs, _) => spec_append(spec_gcalls(e), spec_gcalls_cases(*cs)),
        Stmt::Call(k, nm, args, l) => List::Cons((k, nm, l), Box::new(spec_gcalls_args(*args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => spec_append(spec_gcalls(sq), spec_gcalls_stmts(*body)),
        Stmt::SetIndex(_, i, e, _) => spec_append(spec_gcalls(i), spec_gcalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => spec_append(spec_gcalls(i), spec_gcalls(e)),
        Stmt::PushField(_, e, _) => spec_gcalls(e),
        Stmt::SetThroughField(_, _, e, _) => spec_gcalls(e),
        Stmt::PushBack(_, e, _) => spec_gcalls(e),
        _ => List::Nil,
    }
}

pub open spec fn spec_gcalls_cases(cs: Cases) -> List<(u32, u32, u32)>
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_gcalls_stmts(*body), spec_gcalls_cases(*rest)),
    }
}

pub fn gcalls_stmts(ss: &Stmts) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_stmts(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(gcalls_stmt(s), gcalls_stmts(rest)),
    }
}

pub fn gcalls_stmt(s: &Stmt) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Return(e, _) => gcalls(e),
        Stmt::If(c, t, f, _) => append(gcalls(c), append(gcalls_stmts(t), gcalls_stmts(f))),
        Stmt::Local(_, _, e, _) => gcalls(e),
        Stmt::Assign(_, e, _) => gcalls(e),
        Stmt::While(c, _, body, _) => append(gcalls(c), gcalls_stmts(body)),
        Stmt::For(init, c, step, _, body, _) => append(gcalls_stmt(init), append(gcalls(c), append(gcalls_stmt(step), gcalls_stmts(body)))),
        Stmt::SetField(_, e, _) => gcalls(e),
        Stmt::SetRefField(_, _, e, _) => gcalls(e),
        Stmt::SetOwnField(_, _, e, _) => gcalls(e),
        Stmt::Switch(e, _, cs, _) => append(gcalls(e), gcalls_cases(cs)),
        Stmt::Call(k, nm, args, l) => List::Cons((*k, *nm, *l), Box::new(gcalls_args(args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => append(gcalls(sq), gcalls_stmts(body)),
        Stmt::SetIndex(_, i, e, _) => append(gcalls(i), gcalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => append(gcalls(i), gcalls(e)),
        Stmt::PushField(_, e, _) => gcalls(e),
        Stmt::SetThroughField(_, _, e, _) => gcalls(e),
        Stmt::PushBack(_, e, _) => gcalls(e),
        _ => List::Nil,
    }
}

pub fn gcalls_cases(cs: &Cases) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(gcalls_stmts(body), gcalls_cases(rest)),
    }
}

/// The first global among `todo` that a line lists and that has a type with no rule, decision 0173.
pub open spec fn spec_gtype_bad(cs: Conds, todo: Params) -> Option<Refusal>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, t), rest) => match spec_gline(cs, g) {
            Some(l) => if spec_global_scalar(t) is None {
                Some(Refusal::GlobalType(l))
            } else {
                spec_gtype_bad(cs, *rest)
            },
            None => spec_gtype_bad(cs, *rest),
        },
    }
}

pub fn gtype_bad(cs: &Conds, todo: &Params) -> (r: Option<Refusal>)
    ensures
        r == spec_gtype_bad(*cs, *todo),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, t), rest) => match gline(cs, *g) {
            Some(l) => if global_scalar(*t).is_none() {
                Some(Refusal::GlobalType(l))
            } else {
                gtype_bad(cs, rest)
            },
            None => gtype_bad(cs, rest),
        },
    }
}

/// The line of the first line that lists a global among `todo`.
pub open spec fn spec_glisted(cs: Conds, todo: Params) -> Option<u32>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => match spec_gline(cs, g) {
            Some(l) => Some(l),
            None => spec_glisted(cs, *rest),
        },
    }
}

pub fn glisted(cs: &Conds, todo: &Params) -> (r: Option<u32>)
    ensures
        r == spec_glisted(*cs, *todo),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => match gline(cs, *g) {
            Some(l) => Some(l),
            None => glisted(cs, rest),
        },
    }
}

/// A member function: its first parameter is an object, or it is a constructor.
/// A member that cannot list a global yet: a `const` member function, whose function twin would take no global, or a virtual
/// function. A member that writes its object, a constructor and a destructor can list one, decision 0178.
pub open spec fn spec_gmember(f: Function) -> bool {
    match spec_head_ty(f.params) {
        Some(t) => t is This || t is Iface || t is IfaceMut,
        None => false,
    }
}

pub fn gmember(f: &Function) -> (r: bool)
    ensures
        r == spec_gmember(*f),
{
    match &f.params {
        List::Cons((_, t), _) => matches!(t, Ty::This(_) | Ty::Iface(_) | Ty::IfaceMut(_)),
        List::Nil => false,
    }
}

/// The first implicit parameter among `todo` with the name of a parameter or a local.
pub open spec fn spec_gclash(cs: Conds, todo: Params, hide: Names, line: u32) -> Option<Refusal>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => if spec_has(hide, g) {
            Some(Refusal::GlobalClash(g, match spec_gline(cs, g) {
                Some(l) => l,
                None => line,
            }))
        } else {
            spec_gclash(cs, *rest, hide, line)
        },
    }
}

pub fn gclash(cs: &Conds, todo: &Params, hide: &Names, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_gclash(*cs, *todo, *hide, line),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => if has(hide, *g) {
            Some(Refusal::GlobalClash(*g, match gline(cs, *g) {
                Some(l) => l,
                None => line,
            }))
        } else {
            gclash(cs, rest, hide, line)
        },
    }
}

/// The first global among `cps`, which the callee changes, that the caller gets by value: it lists it on a reads line only.
pub open spec fn spec_greads(cps: Params, gps: Params) -> Option<u32>
    decreases cps,
{
    match cps {
        List::Nil => None,
        List::Cons((g, t), rest) => if t is Mut && match spec_get(gps, g) {
            Some(t2) => !(t2 is Mut),
            None => false,
        } {
            Some(g)
        } else {
            spec_greads(*rest, gps)
        },
    }
}

pub fn greads(cps: &Params, gps: &Params) -> (r: Option<u32>)
    ensures
        r == spec_greads(*cps, *gps),
    decreases cps,
{
    match cps {
        List::Nil => None,
        List::Cons((g, t), rest) => if matches!(t, Ty::Mut(_)) && match get(gps, *g) {
            Some(t2) => !matches!(t2, Ty::Mut(_)),
            None => false,
        } {
            Some(*g)
        } else {
            greads(rest, gps)
        },
    }
}

/// The first call among `calls` to a callee that changes a global that the caller only reads.
pub open spec fn spec_greads_call(calls: List<(u32, u32, u32)>, gs: Params, gps: Params, fs: Fns) -> Option<Refusal>
    decreases calls,
{
    match calls {
        List::Nil => None,
        List::Cons((k, nm, at), rest) => match spec_find(fs, k) {
            Some(cf) => match spec_greads(spec_gparams(cf.conds, gs), gps) {
                Some(g) => Some(Refusal::ReadsOnly(nm, g, at)),
                None => spec_greads_call(*rest, gs, gps, fs),
            },
            None => spec_greads_call(*rest, gs, gps, fs),
        },
    }
}

pub fn greads_call(calls: &List<(u32, u32, u32)>, gs: &Params, gps: &Params, fs: &Fns) -> (r: Option<Refusal>)
    ensures
        r == spec_greads_call(*calls, *gs, *gps, *fs),
    decreases calls,
{
    match calls {
        List::Nil => None,
        List::Cons((k, nm, at), rest) => match find(fs, *k) {
            Some(cf) => match greads(&gparams(&cf.conds, gs), gps) {
                Some(g) => Some(Refusal::ReadsOnly(*nm, g, *at)),
                None => greads_call(rest, gs, gps, fs),
            },
            None => greads_call(rest, gs, gps, fs),
        },
    }
}

/// The refusal of a function under decision 0173, if any: a listed global of a type with no rule, a member function that lists a
/// global, a listed global with the name of a parameter or a local, and a call that changes a global the caller only reads.
pub open spec fn spec_gcheck(f: Function, gs: Params, gps: Params, hide: Names, fs: Fns) -> Option<Refusal> {
    match spec_gtype_bad(f.conds, gs) {
        Some(r) => Some(r),
        None => match spec_glisted(f.conds, gs) {
            Some(l) => if spec_gmember(f) {
                Some(Refusal::MemberGlobal(l))
            } else {
                match spec_gclash(f.conds, gps, hide, f.line) {
                    Some(r) => Some(r),
                    None => spec_greads_call(spec_gcalls_stmts(f.body), gs, gps, fs),
                }
            },
            None => None,
        },
    }
}

pub fn gcheck(f: &Function, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Option<Refusal>)
    ensures
        r == spec_gcheck(*f, *gs, *gps, *hide, *fs),
{
    match gtype_bad(&f.conds, gs) {
        Some(r) => Some(r),
        None => match glisted(&f.conds, gs) {
            Some(l) => if gmember(f) {
                Some(Refusal::MemberGlobal(l))
            } else {
                match gclash(&f.conds, gps, hide, f.line) {
                    Some(r) => Some(r),
                    None => greads_call(&gcalls_stmts(&f.body), gs, gps, fs),
                }
            },
            None => None,
        },
    }
}

/// The lines of a function after the pass: a reads line that names a global is consumed, and each other line also names the
/// globals of the function after its parameters, so a contract finds them, decision 0173.
pub open spec fn spec_gconds(cs: Conds, gs: Params, gnames: Names) -> Conds
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, decl), rest) => if k == CondKind::Reads && match e {
            Expr::Name(n) => spec_get(gs, n) is Some,
            _ => false,
        } {
            spec_gconds(*rest, gs, gnames)
        } else {
            List::Cons((k, e, l, spec_append(decl, gnames)), Box::new(spec_gconds(*rest, gs, gnames)))
        },
    }
}

pub fn gconds(cs: &Conds, gs: &Params, gnames: &Names) -> (r: Conds)
    ensures
        r == spec_gconds(*cs, *gs, *gnames),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, decl), rest) => if *k == CondKind::Reads && match e {
            Expr::Name(n) => get(gs, *n).is_some(),
            _ => false,
        } {
            gconds(rest, gs, gnames)
        } else {
            List::Cons((*k, copy_expr(e), *l, append(copy(decl), copy(gnames))), Box::new(gconds(rest, gs, gnames)))
        },
    }
}

/// No reads line among `cs` names a global of `gs`.
pub open spec fn spec_no_global_reads(cs: Conds, gs: Params) -> bool
    decreases cs,
{
    match cs {
        List::Nil => true,
        List::Cons((k, e, _, _), rest) => !(k == CondKind::Reads && match e {
            Expr::Name(n) => spec_get(gs, n) is Some,
            _ => false,
        }) && spec_no_global_reads(*rest, gs),
    }
}

/// The pass consumes each reads line that names a global, so the translator never refuses one as a word with no rule, decision 0173.
pub proof fn lemma_gconds_consume_reads(cs: Conds, gs: Params, gnames: Names)
    ensures
        spec_no_global_reads(spec_gconds(cs, gs, gnames), gs),
    decreases cs,
{
    match cs {
        List::Cons(_, rest) => lemma_gconds_consume_reads(*rest, gs, gnames),
        List::Nil => {},
    }
}

/// Each function after the pass holds no reads line that names a global.
pub proof fn lemma_globalize_consumes_reads(f: Function, gs: Params, fs: Fns)
    ensures
        spec_no_global_reads(spec_globalize_fn(f, gs, fs).conds, gs),
{
    let gps = spec_gparams(f.conds, gs);
    let hide = spec_append(spec_keys(f.params), spec_glocals(f.body));
    lemma_gconds_consume_reads(f.conds, gs, spec_keys(gps));
    if let Some(r) = spec_gcheck(f, gs, gps, hide, fs) {
        assert(spec_globalize_fn(f, gs, fs).conds == List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(spec_gconds(f.conds, gs, spec_keys(gps)))));
    }
}

/// One function after the pass of decision 0173. A refusal of the pass is a line that the translator refuses first.
pub open spec fn spec_globalize_fn(f: Function, gs: Params, fs: Fns) -> Function {
    let gps = spec_gparams(f.conds, gs);
    let hide = spec_append(spec_keys(f.params), spec_glocals(f.body));
    let cs = spec_gconds(f.conds, gs, spec_keys(gps));
    Function {
        name: f.name,
        line: f.line,
        params: spec_append(f.params, gps),
        ret: f.ret,
        trusted: f.trusted,
        conds: match spec_gcheck(f, gs, gps, hide, fs) {
            Some(r) => List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(cs)),
            None => cs,
        },
        body: spec_gstmts(f.body, gs, gps, hide, fs),
    }
}

pub fn globalize_fn(f: &Function, gs: &Params, fs: &Fns) -> (r: Function)
    ensures
        r == spec_globalize_fn(*f, *gs, *fs),
{
    let gps = gparams(&f.conds, gs);
    let hide = append(keys(&f.params), glocals(&f.body));
    let cs = gconds(&f.conds, gs, &keys(&gps));
    let conds = match gcheck(f, gs, &gps, &hide, fs) {
        Some(r) => List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(cs)),
        None => cs,
    };
    let body = gstmts(&f.body, gs, &gps, &hide, fs);
    Function { name: f.name, line: f.line, params: append(copy(&f.params), gps), ret: f.ret, trusted: f.trusted, conds, body }
}

pub open spec fn spec_globalize_all(todo: Fns, gs: Params, fs: Fns) -> Fns
    decreases todo,
{
    match todo {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(Box::new(spec_globalize_fn(*f, gs, fs)), Box::new(spec_globalize_all(*rest, gs, fs))),
    }
}

pub fn globalize_all(todo: &Fns, gs: &Params, fs: &Fns) -> (r: Fns)
    ensures
        r == spec_globalize_all(*todo, *gs, *fs),
    decreases todo,
{
    match todo {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(Box::new(globalize_fn(f, gs, fs)), Box::new(globalize_all(rest, gs, fs))),
    }
}

/// The pass of decision 0173, which the shell runs before translate_unit: each function of the file with the globals `gs` that it
/// lists as implicit parameters.
pub open spec fn spec_globalize(fs: Fns, gs: Params) -> Fns {
    spec_globalize_all(fs, gs, fs)
}

pub fn globalize(fs: &Fns, gs: &Params) -> (r: Fns)
    ensures
        r == spec_globalize(*fs, *gs),
{
    globalize_all(fs, gs, fs)
}

} // verus!

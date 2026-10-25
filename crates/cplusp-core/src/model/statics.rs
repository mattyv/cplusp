//! The translator: static member functions, decision 0174. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ static member functions, decision 0174

/// A static member function of a struct of the file by the id of its name: a member whose twin takes no object, `this` of a struct
/// or of an interface. A static can take a struct as its first argument. A static has its
/// qualified name, `Tally::valid`, so it never meets a const member, whose name is plain. A member with no twin is taken as a
/// static here too, so a contract that calls it is refused.
// ponytail: a companion function with the plain name of a member with no twin of some struct is refused as no pure member
// function. Upgrade: a flag for a static in the table of members.
pub open spec fn spec_static(sd: Structs, f: u32) -> Option<(u32, Option<(Ty, Params)>)>
    decreases sd,
{
    match sd {
        List::Nil => None,
        List::Cons((_, (_, _, ms)), rest) => match spec_get(ms, f) {
            Some((key, Some((t, mps)))) => if spec_head_ty(mps) is Some && (spec_head_ty(mps)->Some_0 is This || spec_head_ty(mps)->Some_0 is Iface) {
                spec_static(*rest, f)
            } else {
                Some((key, Some((t, mps))))
            },
            Some((key, None)) => Some((key, None)),
            None => spec_static(*rest, f),
        },
    }
}

pub fn static_of(sd: &Structs, f: u32) -> (r: Option<(u32, Option<(Ty, Params)>)>)
    ensures
        r == spec_static(*sd, f),
    decreases sd,
{
    match sd {
        List::Nil => None,
        List::Cons((_, (_, _, ms)), rest) => match get_ref(ms, f) {
            Some((key, Some((t, mps)))) => if match mps {
                List::Cons((_, t0), _) => matches!(t0, Ty::This(_) | Ty::Iface(_)),
                List::Nil => false,
            } {
                static_of(rest, f)
            } else {
                Some((*key, Some((*t, copy(mps)))))
            },
            Some((key, None)) => Some((*key, None)),
            None => static_of(rest, f),
        },
    }
}

/// The parameters of a twin after those that the arguments of the call fill.
pub open spec fn spec_drop_params(mps: Params, args: Args) -> Params
    decreases args,
{
    match args {
        List::Nil => mps,
        List::Cons(_, rest) => match mps {
            List::Nil => List::Nil,
            List::Cons(_, prest) => spec_drop_params(*prest, *rest),
        },
    }
}

pub fn drop_params(mps: &Params, args: &Args) -> (r: Params)
    ensures
        r == spec_drop_params(*mps, *args),
    decreases args,
{
    match args {
        List::Nil => copy(mps),
        List::Cons(_, rest) => match mps {
            List::Nil => List::Nil,
            List::Cons(_, prest) => drop_params(prest, rest),
        },
    }
}

/// The values of the globals `gps` of a twin, as the contract line reads each by its name: before in a requires line and under
/// `old`, after in an ensures line. A global that the function lists on no line is no parameter, so the line is refused.
pub open spec fn spec_gvals(gps: Params, decl: Names, ps: Params, line: u32) -> Result<DArgs, Refusal>
    decreases gps,
{
    match gps {
        List::Nil => Ok(List::Nil),
        List::Cons((g, _), rest) => match spec_rebind(decl, ps, g) {
            Some((p, t)) => match spec_gvals(*rest, decl, ps, line) {
                Ok(dr) => Ok(List::Cons(spec_var(p, t), Box::new(dr))),
                Err(r) => Err(r),
            },
            None => Err(Refusal::Name(g, line)),
        },
    }
}

pub fn gvals(gps: &Params, decl: &Names, ps: &Params, line: u32) -> (r: Result<DArgs, Refusal>)
    ensures
        r == spec_gvals(*gps, *decl, *ps, line),
    decreases gps,
{
    match gps {
        List::Nil => Ok(List::Nil),
        List::Cons((g, _), rest) => match rebind(decl, ps, *g) {
            Some((p, t)) => match gvals(rest, decl, ps, line) {
                Ok(dr) => Ok(List::Cons(contract_var(p, t), Box::new(dr))),
                Err(r) => Err(r),
            },
            None => Err(Refusal::Name(*g, line)),
        },
    }
}

/// A call `f(a)` of a contract with the arguments `da` that names no member of the object: the twin of a static member function
/// with its globals after the arguments, decision 0174, or else a function of the companion file, decision 0079.
pub open spec fn spec_static_value(f: u32, da: DArgs, args: Args, decl: Names, ps: Params, line: u32, sd: Structs) -> Result<DExpr, Refusal> {
    match spec_static(sd, f) {
        Some((key, Some((t, mps)))) => match spec_gvals(spec_drop_params(mps, args), decl, ps, line) {
            Ok(dg) => spec_leaf(DExpr::FCall(key, Box::new(spec_append(spec_convert(da, mps), dg))), t, line),
            Err(r) => Err(r),
        },
        Some((_, None)) => Err(Refusal::NotPure(f, line)),
        None => Ok(DExpr::Apply(f, Box::new(da))),
    }
}

pub fn static_value(f: u32, da: DArgs, args: &Args, decl: &Names, ps: &Params, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_static_value(f, da, *args, *decl, *ps, line, *sd),
{
    match static_of(sd, f) {
        Some((key, Some((t, mps)))) => match gvals(&drop_params(&mps, args), decl, ps, line) {
            Ok(dg) => translate_leaf(DExpr::FCall(key, Box::new(append(convert(da, &mps), dg))), t, line),
            Err(r) => Err(r),
        },
        Some((_, None)) => Err(Refusal::NotPure(f, line)),
        None => Ok(DExpr::Apply(f, Box::new(da))),
    }
}

} // verus!

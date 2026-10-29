//! The translator: virtual functions, decision 0165. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ virtual functions, decision 0165

/// The check of one override. `base` and `derived` are the keys of the function of the interface and of the override. `params` are
/// the parameters of the override after `this`. `requires` and `ensures` are the contract of the function of the interface, read on
/// the parameters of the override. `own` is the requires lines of the override. Dafny proves that `own` follows from `requires`, and
/// that the function of the override meets `ensures`. `promise` is the ensures lines of the override. An override that writes has
/// no function, so Dafny proves that `promise` gives `ensures`, decision 0169.
#[derive(PartialEq, Eq, Debug)]
pub struct DOverride {
    pub base: u32,
    pub derived: u32,
    pub params: DParams,
    pub ret: DTy,
    pub requires: DConds,
    pub ensures: DConds,
    pub own: DConds,
    pub promise: DConds,
}

pub type DOverrides = List<DOverride>;

/// The upcast from the final class `derived` to the interface `base`, with the check of each override.
#[derive(PartialEq, Eq, Debug)]
pub struct DUpcast {
    pub derived: u32,
    pub base: u32,
    pub overrides: DOverrides,
}

/// The parameters have the same types in their order, whatever their names.
pub open spec fn spec_same_tys(a: Params, b: Params) -> bool
    decreases a,
{
    match a {
        List::Nil => b == List::<(u32, Ty)>::Nil,
        List::Cons((_, ta), ra) => match b {
            List::Cons((_, tb), rb) => ta == tb && spec_same_tys(*ra, *rb),
            List::Nil => false,
        },
    }
}

/// The type of the first parameter, `this` of a member function.
pub open spec fn spec_head_ty(ps: Params) -> Option<Ty> {
    match ps {
        List::Cons((_, t), _) => Some(t),
        List::Nil => None,
    }
}

/// The function `fb` of the interface `b` and the function `fd` of the class `d` have the same parameters after `this` and the
/// same result.
pub open spec fn spec_overrides_fn(fb: Function, fd: Function, d: u32, b: u32) -> bool {
    ((spec_head_ty(fb.params) == Some(Ty::Iface(b)) && spec_head_ty(fd.params) == Some(Ty::This(d))) || (spec_head_ty(fb.params) == Some(
        Ty::IfaceMut(b),
    ) && spec_head_ty(fd.params) == Some(Ty::ThisMut(d)))) && fb.ret == fd.ret && spec_same_tys(spec_tail(fb.params), spec_tail(fd.params))
}

/// The check of the function `fb` of the interface on its override `fd`. The contract of `fb` reads the parameters of `fd` by their
/// place, decision 0060.
pub open spec fn spec_check(fb: Function, fd: Function, sd: Structs) -> Result<DOverride, Refusal> {
    match spec_params(spec_tail(fd.params), fd.line, sd) {
        Err(r) => Err(r),
        Ok(ps) => match spec_ret_ty(fd.ret, fd.line, sd) {
            Err(r) => Err(r),
            Ok(ret) => match spec_conds(fb.conds, CondKind::Requires, fd.params, fd.ret, sd) {
                Err(r) => Err(r),
                Ok(rq) => match spec_conds(fb.conds, CondKind::Ensures, fd.params, fd.ret, sd) {
                    Err(r) => Err(r),
                    Ok(en) => match spec_conds(fd.conds, CondKind::Requires, fd.params, fd.ret, sd) {
                        Err(r) => Err(r),
                        Ok(own) => match spec_conds(fd.conds, CondKind::Ensures, fd.params, fd.ret, sd) {
                            Err(r) => Err(r),
                            Ok(promise) => Ok(DOverride { base: fb.name, derived: fd.name, params: ps, ret, requires: rq, ensures: en, own, promise }),
                        },
                    },
                },
            },
        },
    }
}

/// The check of the override in the class `d` of the virtual function `n` of the interface `b`, whose function has the key `bk`.
/// `line` is the line of `d`. The override must have the same parameters and result, and a function in the model, decision 0090.
pub open spec fn spec_override(d: u32, b: u32, n: u32, bk: u32, line: u32, all: Fns, sd: Structs) -> Result<DOverride, Refusal> {
    match spec_member(sd, d, n) {
        None => Err(Refusal::NoOverride(d, b, n, line)),
        Some((dk, pure)) => match spec_find(all, bk) {
            None => Err(Refusal::NoOverride(d, b, n, line)),
            Some(fb) => match spec_find(all, dk) {
                None => Err(Refusal::NoOverride(d, b, n, line)),
                Some(fd) => if !spec_overrides_fn(fb, fd, d, b) {
                    Err(Refusal::NoOverride(d, b, n, line))
                } else if spec_const_virtual(fb) && pure is None {
                    Err(Refusal::Unchecked(d, b, n, line))
                } else if !spec_const_virtual(fb) && !(spec_function(fd, all, sd) is Full) {
                    // An override that writes is checked on its contract, so it must have a method, decision 0169.
                    Err(Refusal::NoMethod(d, b, n, line))
                } else {
                    // The contract of the interface must have a model of its own, decision 0166.
                    match spec_inside_of(fb, all, sd) {
                        Err(r) => Err(r),
                        Ok(_) => spec_check(fb, fd, sd),
                    }
                },
            },
        },
    }
}

/// The checks of the overrides in `d` of the members `ms` of the interface `b`, or the first refusal.
pub open spec fn spec_override_each(d: u32, b: u32, ms: Members, line: u32, all: Fns, sd: Structs) -> Result<DOverrides, Refusal>
    decreases ms,
{
    match ms {
        List::Nil => Ok(List::Nil),
        List::Cons((n, (bk, _)), rest) => match spec_override(d, b, n, bk, line, all, sd) {
            Err(r) => Err(r),
            Ok(o) => match spec_override_each(d, b, *rest, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(List::Cons(o, Box::new(os))),
            },
        },
    }
}

/// The function that `spec_find` gives has the key it was asked for.
pub proof fn lemma_find_has_the_key(fs: Fns, key: u32)
    ensures
        match spec_find(fs, key) {
            Some(f) => f.name == key,
            None => true,
        },
    decreases fs,
{
    match fs {
        List::Nil => {},
        List::Cons(f, rest) => if f.name != key {
            lemma_find_has_the_key(*rest, key);
        },
    }
}

/// The checks `os` are one for each member of the interface `b` in `ms`, in their order. Each is of the member of `d` with the same
/// name, which has a function in the model and the same parameters and result.
pub open spec fn spec_checked(d: u32, b: u32, ms: Members, os: DOverrides, all: Fns, sd: Structs) -> bool
    decreases ms,
{
    match ms {
        List::Nil => os == List::<DOverride>::Nil,
        List::Cons((n, (bk, _)), rest) => match os {
            List::Nil => false,
            List::Cons(o, orest) => o.base == bk && match spec_member(sd, d, n) {
                Some((dk, p)) => o.derived == dk && match spec_find(all, bk) {
                    Some(fb) => match spec_find(all, dk) {
                        // A const override has a function in the model, and one that writes has a method, decision 0169.
                        Some(fd) => spec_overrides_fn(fb, fd, d, b) && (if spec_const_virtual(fb) {
                            p is Some
                        } else {
                            spec_function(fd, all, sd) is Full
                        }),
                        None => false,
                    },
                    None => false,
                },
                _ => false,
            } && spec_checked(d, b, *rest, *orest, all, sd),
        },
    }
}

/// The checks of the members of an interface are one for each member, in their order, each of an override with the same signature
/// and a function in the model.
pub proof fn lemma_each_member_is_checked(d: u32, b: u32, ms: Members, line: u32, all: Fns, sd: Structs)
    ensures
        match spec_override_each(d, b, ms, line, all, sd) {
            Ok(os) => spec_checked(d, b, ms, os, all, sd),
            Err(_) => true,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((n, (bk, _)), rest) => {
            lemma_find_has_the_key(all, bk);
            match spec_member(sd, d, n) {
                Some((dk, _)) => lemma_find_has_the_key(all, dk),
                None => {},
            }
            lemma_each_member_is_checked(d, b, *rest, line, all, sd);
        },
    }
}

/// A member of the table has the function `key`.
pub open spec fn spec_keyed(ms: Members, key: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (k, _)), rest) => k == key || spec_keyed(*rest, key),
    }
}

/// Each function of `fs` whose first parameter is `this` of the interface `b` is in its member table `ms`. The plugin leaves out
/// a name that two functions share, decision 0090. A free function of `const B&` has `IfaceRef`, so it is none of them.
pub open spec fn spec_listed(fs: Fns, b: u32, ms: Members) -> bool
    decreases fs,
{
    match fs {
        List::Nil => true,
        List::Cons(f, rest) => (spec_virtual(*f) != Some(b) || spec_keyed(ms, f.name)) && spec_listed(*rest, b, ms),
    }
}

/// The upcast from the final class `d`, at the line `line`, to the interface `b`. The shell sends the interface from its table.
pub open spec fn spec_upcast(d: u32, b: u32, line: u32, all: Fns, sd: Structs) -> Result<DUpcast, Refusal> {
    match spec_get(sd, b) {
        None => Err(Refusal::Syntax(line)),
        Some((bl, _, ms)) => if !spec_listed(all, b, ms) {
            Err(Refusal::Overload(b, bl))
        } else {
            match spec_override_each(d, b, ms, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(DUpcast { derived: d, base: b, overrides: os }),
            }
        },
    }
}

/// An upcast holds only with a check of each virtual function of the interface. Each function with `this` of the interface is in
/// its member table, and each member has its check. A class with a virtual function with no override, or with an override that has
/// another signature or no function in the model, and an interface with two virtual functions of one name, have no upcast, decision
/// 0165.
pub proof fn lemma_each_virtual_function_is_checked(d: u32, b: u32, line: u32, all: Fns, sd: Structs)
    ensures
        match spec_upcast(d, b, line, all, sd) {
            Ok(up) => match spec_get(sd, b) {
                Some((_, _, ms)) => spec_listed(all, b, ms) && spec_checked(d, b, ms, up.overrides, all, sd),
                None => false,
            },
            Err(_) => true,
        },
{
    match spec_get(sd, b) {
        Some((_, _, ms)) => lemma_each_member_is_checked(d, b, ms, line, all, sd),
        None => {},
    }
}

/// The upcasts from the final class `d` to each of its interfaces `bs`, in their order.
pub open spec fn spec_upcasts_of(d: u32, bs: Names, line: u32, all: Fns, sd: Structs) -> List<Result<DUpcast, Refusal>>
    decreases bs,
{
    match bs {
        List::Nil => List::Nil,
        List::Cons(b, rest) => List::Cons(spec_upcast(d, b, line, all, sd), Box::new(spec_upcasts_of(d, *rest, line, all, sd))),
    }
}

/// The upcasts of each class over interfaces, by its key, the keys of its interfaces and whether it is final, in their order. A
/// class that is not final has none, and its refusal. The shell sends each class from its table.
pub open spec fn spec_upcasts(bases: List<(u32, (Names, bool))>, all: Fns, sd: Structs) -> List<Result<DUpcast, Refusal>>
    decreases bases,
{
    match bases {
        List::Nil => List::Nil,
        List::Cons((d, (bs, fin)), rest) => match spec_get(sd, d) {
            None => List::Cons(Err(Refusal::Syntax(0)), Box::new(spec_upcasts(*rest, all, sd))),
            Some((line, _, _)) => if !fin {
                List::Cons(Err(Refusal::NotFinal(d, line)), Box::new(spec_upcasts(*rest, all, sd)))
            } else {
                spec_append(spec_upcasts_of(d, bs, line, all, sd), spec_upcasts(*rest, all, sd))
            },
        },
    }
}

/// The type of Dafny of an integer type of C++.
pub open spec fn spec_int_dty(t: Ty) -> Option<DTy> {
    match t {
        Ty::I32 => Some(DTy::Int32),
        Ty::I64 => Some(DTy::Int64),
        Ty::U8 => Some(DTy::UInt8),
        Ty::U32 => Some(DTy::UInt32),
        Ty::U64 => Some(DTy::UInt64),
        Ty::I8 => Some(DTy::Int8),
        Ty::I16 => Some(DTy::Int16),
        Ty::U16 => Some(DTy::UInt16),
        _ => None,
    }
}

/// The parameters after `this`.
pub open spec fn spec_tail(ps: Params) -> Params {
    match ps {
        List::Cons((_, _), rest) => *rest,
        List::Nil => List::Nil,
    }
}

/// The arguments of a contract call, each exact integer as `(e as T)` for its parameter of type `T`, decision 0095.
pub open spec fn spec_convert(da: DArgs, ps: Params) -> DArgs
    decreases da,
{
    match da {
        List::Nil => List::Nil,
        List::Cons(d, rest) => match ps {
            List::Cons((_, t), prest) => List::Cons(
                match spec_int_dty(t) {
                    Some(dt) => DExpr::Conv(dt, Box::new(d)),
                    None => d,
                },
                Box::new(spec_convert(*rest, *prest))),
            List::Nil => List::Cons(d, Box::new(spec_convert(*rest, List::Nil))),
        },
    }
}

/// True when a Dafny expression calls the function of a pure member function, decision 0215.
pub open spec fn spec_calls(d: DExpr) -> bool
    decreases d,
{
    match d {
        DExpr::Lit(_) => false,
        DExpr::Bool(_) => false,
        DExpr::Var(_) => false,
        DExpr::Result => false,
        DExpr::Bin(_, x1, x2) => spec_calls(*x1) || spec_calls(*x2),
        DExpr::Not(x0) => spec_calls(*x0),
        DExpr::Neg(x0) => spec_calls(*x0),
        DExpr::AsInt(x0) => spec_calls(*x0),
        DExpr::Conv(_, x1) => spec_calls(*x1),
        DExpr::Len(x0) => spec_calls(*x0),
        DExpr::Index(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::Forall(_, x1) => spec_calls(*x1),
        DExpr::Exists(_, x1) => spec_calls(*x1),
        DExpr::Bound(_) => false,
        DExpr::Chain(_, _, x2, x3, x4) => spec_calls(*x2) || spec_calls(*x3) || spec_calls(*x4),
        DExpr::Field(x0, _) => spec_calls(*x0),
        DExpr::Ctor(_, x1) => spec_calls_any(*x1),
        DExpr::IsSome(x0) => spec_calls(*x0),
        DExpr::Get(x0) => spec_calls(*x0),
        DExpr::Is(_, x1) => spec_calls(*x1),
        DExpr::Alt(_, x1) => spec_calls(*x1),
        DExpr::Nothing => false,
        DExpr::Just(x0) => spec_calls(*x0),
        DExpr::Drop(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::Apply(_, x1) => spec_calls_any(*x1),
        DExpr::Take(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::Slice(x0, x1, x2) => spec_calls(*x0) || spec_calls(*x1) || spec_calls(*x2),
        DExpr::TDiv(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::TRem(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::DivIn(x0, x1, _) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::RemIn(x0, x1, _) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::FCall(_, _) => true,
        DExpr::After => false,
        DExpr::Out(_) => false,
        DExpr::Enumerator(_, _) => false,
        DExpr::Ite(x0, x1, x2) => spec_calls(*x0) || spec_calls(*x1) || spec_calls(*x2),
        DExpr::Temp(_) => false,
        DExpr::ShrIn(x0, x1, _, _) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::SetAt(x0, x1, x2) => spec_calls(*x0) || spec_calls(*x1) || spec_calls(*x2),
        DExpr::Append(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::CountIf(x0, _, _, x3) => spec_calls(*x0) || spec_calls(*x3),
        DExpr::RealLit(_, _) => false,
        DExpr::FOp(_, x1, x2) => spec_calls(*x1) || spec_calls(*x2),
        DExpr::Abs(x0) => spec_calls(*x0),
        DExpr::FromInt(x0) => spec_calls(*x0),
        DExpr::Upcast(_, _, x2) => spec_calls(*x2),
        DExpr::Lemma(_, x1, x2) => spec_calls(*x2) || spec_calls_any(*x1),
        DExpr::Let(_, _, x2, x3) => spec_calls(*x2) || spec_calls(*x3),
        DExpr::BitOp(_, x1, x2) => spec_calls(*x1) || spec_calls(*x2),
        DExpr::SeqLit(x0) => spec_calls_any(*x0),
        DExpr::EmptySeq => false,
        DExpr::SeqFill(x0, x1) => spec_calls(*x0) || spec_calls(*x1),
        DExpr::Back(x0) => spec_calls(*x0),
        DExpr::PopBack(x0) => spec_calls(*x0),
        DExpr::IntAbs(x0) => spec_calls(*x0),
        DExpr::Eps => false,
        DExpr::Eta => false,
        DExpr::DblMax => false,
    }
}

pub open spec fn spec_calls_any(a: DArgs) -> bool
    decreases a,
{
    match a {
        List::Nil => false,
        List::Cons(d, rest) => spec_calls(d) || spec_calls_any(*rest),
    }
}

/// The ensures lines that call no function of a pure member function. They go on the function of a pure body, decisions 0213
/// and 0215. A line that calls one stays on the method, so two functions whose lines call each other make no cycle in Dafny.
pub open spec fn spec_no_calls(cs: DConds) -> DConds
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((d, l), rest) => if spec_calls(d) {
            spec_no_calls(*rest)
        } else {
            List::Cons((d, l), Box::new(spec_no_calls(*rest)))
        },
    }
}

/// The model of a function among the functions `all` of its file, decision 0058.
pub open spec fn spec_function(f: Function, all: Fns, sd: Structs) -> Model {
    match spec_params(f.params, f.line, sd) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match spec_ret_ty(f.ret, f.line, sd) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match spec_checks(f) {
                Some(r) => Model::Refused(r),
                None => match spec_braces(f.body, spec_fixed(f.ret)) {
                Some(r) => Model::Bare(f.name, ps, ret, r),
                None => match spec_inside_of(f, all, sd) {
                    Err(r) => Model::Bare(f.name, ps, ret, r),
                    Ok((req, ens, dec, body)) => Model::Full(
                        Method {
                            name: f.name,
                            params: ps,
                            ret,
                            requires: spec_bounds(f.params, f.line, req),
                            ensures: spec_ret_len(f.ret, f.line, spec_linked(f, ens, spec_member_fn(f, ens, body, all, sd))),
                            decreases: dec,
                            body,
                            function: spec_member_fn(f, ens, body, all, sd),
                            fensures: if spec_pure_body(f.params, body, all, sd, spec_static_key(sd, f.name)) is Some {
                                spec_no_calls(ens)
                            } else {
                                List::Nil
                            },
                            writes: spec_writes(f.params),
                            outs: spec_outs(f.params),
                            trusted: f.trusted,
                        },
                    ),
                },
                },
            },
        },
    }
}

/// The checks of a signature with its contract: the modifies lines, decision 0108, and the words that keep NaN out, decision 0150.
pub open spec fn spec_checks(f: Function) -> Option<Refusal> {
    // A line that the translator cannot read gets its own refusal first, decision 0155. The pass of decision 0173 puts its
    // refusal on such a line.
    if spec_any_bad(f.conds) {
        None
    } else {
        match spec_modifies(f.params, f.conds, f.line) {
            Some(r) => Some(r),
            None => spec_finite(f.params, f.conds, f.trusted, f.ret, f.line),
        }
    }
}

/// The model holds no NaN and no infinity. So each double parameter needs `std::isfinite` of it in a requires line, and a trusted
/// function that gives a double needs `std::isfinite(result)` in an ensures line, decision 0150.
pub open spec fn spec_finite(ps: Params, cs: Conds, trusted: bool, ret: Ty, line: u32) -> Option<Refusal> {
    // A line that the translator cannot read gets its own refusal first, decision 0155.
    if spec_any_bad(cs) {
        None
    } else {
    match spec_unfinite(ps, ps, cs) {
        Some(p) => Some(Refusal::Finite(p, line)),
        None => if trusted && ret == Ty::F64 && !spec_finite_result(cs) {
            Some(Refusal::FiniteResult(line))
        } else {
            None
        },
    }
    }
}

/// A contract line that the shell could not cut or parse.
pub open spec fn spec_any_bad(cs: Conds) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _, _), rest) => k is Bad || spec_any_bad(*rest),
    }
}

pub fn any_bad(cs: &Conds) -> (r: bool)
    ensures
        r == spec_any_bad(*cs),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _, _), rest) => (match k {
            CondKind::Bad(_) => true,
            _ => false,
        }) || any_bad(rest),
    }
}

/// The first double parameter among `todo` that no requires line says is finite.
pub open spec fn spec_unfinite(todo: Params, ps: Params, cs: Conds) -> Option<u32>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => if t == Ty::F64 && !spec_finite_said(ps, cs, p) {
            Some(p)
        } else {
            spec_unfinite(*rest, ps, cs)
        },
    }
}

/// A requires line says that the parameter `p` is finite.
pub open spec fn spec_finite_said(ps: Params, cs: Conds, p: u32) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => (k == CondKind::Requires && spec_says_finite(e, decl, ps, p)) || spec_finite_said(ps, *rest, p),
    }
}

/// `std::isfinite(x)` of the parameter `p`, alone or as a part joined by `&&`.
pub open spec fn spec_says_finite(e: Expr, decl: Names, ps: Params, p: u32) -> bool
    decreases e,
{
    match e {
        Expr::Finite(a) => match *a {
            Expr::Name(n) => match spec_rebind(decl, ps, n) {
                Some((q, _)) => q == p,
                None => false,
            },
            _ => false,
        },
        Expr::Bin(op, a, b) => op == BinOp::And && (spec_says_finite(*a, decl, ps, p) || spec_says_finite(*b, decl, ps, p)),
        Expr::Paren(a) => spec_says_finite(*a, decl, ps, p),
        _ => false,
    }
}

/// An ensures line says that the result is finite.
pub open spec fn spec_finite_result(cs: Conds) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, _), rest) => (k == CondKind::Ensures && spec_says_result_finite(e)) || spec_finite_result(*rest),
    }
}

/// `std::isfinite(result)`, alone or as a part joined by `&&`.
pub open spec fn spec_says_result_finite(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Finite(a) => *a is Result,
        Expr::Bin(op, a, b) => op == BinOp::And && (spec_says_result_finite(*a) || spec_says_result_finite(*b)),
        Expr::Paren(a) => spec_says_result_finite(*a),
        _ => false,
    }
}

pub fn checks(f: &Function) -> (r: Option<Refusal>)
    ensures
        r == spec_checks(*f),
{
    if any_bad(&f.conds) {
        None
    } else {
        match modifies(&f.params, &f.conds, f.line) {
            Some(r) => Some(r),
            None => finite(&f.params, &f.conds, f.trusted, f.ret, f.line),
        }
    }
}

pub fn finite(ps: &Params, cs: &Conds, trusted: bool, ret: Ty, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_finite(*ps, *cs, trusted, ret, line),
{
    if any_bad(cs) {
        return None;
    }
    match unfinite(ps, ps, cs) {
        Some(p) => Some(Refusal::Finite(p, line)),
        None => if trusted && ret == Ty::F64 && !finite_result(cs) {
            Some(Refusal::FiniteResult(line))
        } else {
            None
        },
    }
}

pub fn unfinite(todo: &Params, ps: &Params, cs: &Conds) -> (r: Option<u32>)
    ensures
        r == spec_unfinite(*todo, *ps, *cs),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => if *t == Ty::F64 && !finite_said(ps, cs, *p) {
            Some(*p)
        } else {
            unfinite(rest, ps, cs)
        },
    }
}

pub fn finite_said(ps: &Params, cs: &Conds, p: u32) -> (r: bool)
    ensures
        r == spec_finite_said(*ps, *cs, p),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => (*k == CondKind::Requires && says_finite(e, decl, ps, p)) || finite_said(ps, rest, p),
    }
}

pub fn says_finite(e: &Expr, decl: &Names, ps: &Params, p: u32) -> (r: bool)
    ensures
        r == spec_says_finite(*e, *decl, *ps, p),
    decreases e,
{
    match e {
        Expr::Finite(a) => match &**a {
            Expr::Name(n) => match rebind(decl, ps, *n) {
                Some((q, _)) => q == p,
                None => false,
            },
            _ => false,
        },
        Expr::Bin(op, a, b) => *op == BinOp::And && (says_finite(a, decl, ps, p) || says_finite(b, decl, ps, p)),
        Expr::Paren(a) => says_finite(a, decl, ps, p),
        _ => false,
    }
}

pub fn finite_result(cs: &Conds) -> (r: bool)
    ensures
        r == spec_finite_result(*cs),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, _), rest) => (*k == CondKind::Ensures && says_result_finite(e)) || finite_result(rest),
    }
}

pub fn says_result_finite(e: &Expr) -> (r: bool)
    ensures
        r == spec_says_result_finite(*e),
    decreases e,
{
    match e {
        Expr::Finite(a) => match &**a {
            Expr::Result => true,
            _ => false,
        },
        Expr::Bin(op, a, b) => *op == BinOp::And && (says_result_finite(a) || says_result_finite(b)),
        Expr::Paren(a) => says_result_finite(a),
        _ => false,
    }
}

/// The type of a field: a type of the subset, and a `std::array` as a sequence that holds its length, decision 0196.
pub open spec fn spec_field_dty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::Seq(s, Extent::Fixed(k)) => match spec_ty(t, line) {
            Ok(_) => Ok(DTy::Arr(s, k)),
            Err(r) => Err(r),
        },
        _ => spec_ty(t, line),
    }
}

pub fn field_dty(t: Ty, line: u32) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_field_dty(t, line),
{
    match t {
        Ty::Seq(s, Extent::Fixed(k)) => match translate_ty(t, line) {
            Ok(_) => Ok(DTy::Arr(s, k)),
            Err(r) => Err(r),
        },
        _ => translate_ty(t, line),
    }
}

/// The model of a struct: each field a type of the subset, decision 0073. A field can be a sequence, decision 0076.
pub open spec fn spec_fields(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        // An optional of a struct is no field yet, decision 0137. A unique_ptr of a struct or an interface is a field, decision 0171.
        List::Cons((n, t), rest) => match (if (t is Opt && t->Opt_0 is Struct) || t is Ptr || (t is Own && !(t->Own_0 is Struct)) || t is F64 { Err(Refusal::Element(line)) } else { spec_field_dty(t, line) }) {
            Ok(dt) => match spec_fields(*rest, line) {
                Ok(dr) => Ok(List::Cons((n, dt), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub open spec fn spec_structs(sd: Structs) -> StructModels {
    spec_structs_in(sd, sd)
}

/// A field that holds a struct with a destructor.
pub open spec fn spec_dtor_field(fields: Params, sd: Structs) -> bool
    decreases fields,
{
    match fields {
        List::Nil => false,
        List::Cons((_, t), rest) => spec_holds_dtor(t, sd) || spec_dtor_field(*rest, sd),
    }
}

pub fn dtor_field(fields: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_dtor_field(*fields, *sd),
    decreases fields,
{
    match fields {
        List::Nil => false,
        List::Cons((_, t), rest) => holds_dtor(*t, sd) || dtor_field(rest, sd),
    }
}

/// The models of the structs `sd` among the structs `all` of the file. A field of a struct with a destructor is a copy, at the
/// line of the struct, decision 0178.
pub open spec fn spec_structs_in(sd: Structs, all: Structs) -> StructModels
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, _)), rest) => List::Cons(
            if spec_dtor_field(fields, all) {
                Err(Refusal::Copy(l))
            } else {
                match spec_fields(fields, l) {
                    Ok(df) => Ok((k, df)),
                    Err(r) => Err(r),
                }
            },
            Box::new(spec_structs_in(*rest, all))),
    }
}

/// The models of the functions `fs`, each among the functions `all` of the file.
pub open spec fn spec_unit(fs: Fns, all: Fns, sd: Structs) -> Models
    decreases fs,
{
    match fs {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(spec_function(*f, all, sd), Box::new(spec_unit(*rest, all, sd))),
    }
}

// ------------------------------------------------------------------ a backed interface, decision 0217

/// The classes of the file over interfaces: the key of each, the keys of its interfaces, and whether it is final.
pub type Bases = List<(u32, (Names, bool))>;

/// The interface of a virtual function: the class of its `this`, decisions 0165 and 0169.
pub open spec fn spec_iface_of(f: Function) -> Option<u32> {
    match spec_head_ty(f.params) {
        Some(Ty::Iface(k)) => Some(k),
        Some(Ty::IfaceMut(k)) => Some(k),
        _ => None,
    }
}

/// A final class of the file has the interface `k`.
pub open spec fn spec_over(bases: Bases, k: u32) -> bool
    decreases bases,
{
    match bases {
        List::Nil => false,
        List::Cons((_, (bs, fin)), rest) => (fin && spec_has(bs, k)) || spec_over(*rest, k),
    }
}

/// The interface of each virtual function of `fs` has a final class over it in the file, decision 0217.
pub open spec fn spec_backed(fs: Fns, bases: Bases) -> bool
    decreases fs,
{
    match fs {
        List::Nil => true,
        List::Cons(f, rest) => match spec_iface_of(*f) {
            Some(k) => spec_over(bases, k) && spec_backed(*rest, bases),
            None => spec_backed(*rest, bases),
        },
    }
}

/// A place is a local through its interface, decision 0208.
pub open spec fn spec_objs_down(os: Objs) -> bool
    decreases os,
{
    match os {
        List::Nil => false,
        List::Cons(o, rest) => o is Down || spec_objs_down(*rest),
    }
}

pub open spec fn spec_calls_down(cs: DCalls) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons(p, rest) => match p {
            DPre::Update(_, _, os, _, _) => spec_objs_down(os) || spec_calls_down(*rest),
            _ => spec_calls_down(*rest),
        },
    }
}

/// The line of the first statement that writes a local back through its interface, decision 0208.
pub open spec fn spec_down_line(ss: DStmts) -> Option<u32>
    decreases ss,
{
    match ss {
        List::Nil => None,
        List::Cons((s, l), rest) => match spec_stmt_down(*s, l) {
            Some(x) => Some(x),
            None => spec_down_line(*rest),
        },
    }
}

pub open spec fn spec_cases_down(cs: DCases) -> Option<u32>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, b), rest) => match spec_down_line(*b) {
            Some(x) => Some(x),
            None => spec_cases_down(*rest),
        },
    }
}

/// The line of a statement at the line `l` that writes a local back through its interface, or of one inside it.
pub open spec fn spec_stmt_down(s: DStmt, l: u32) -> Option<u32>
    decreases s,
{
    match s {
        DStmt::ReturnUpdate(os, _, _) => if spec_objs_down(os) { Some(l) } else { None },
        DStmt::Update(os, _, _) => if spec_objs_down(os) { Some(l) } else { None },
        DStmt::UpdateAt(o, _, os, _, _) => if o is Down || spec_objs_down(os) { Some(l) } else { None },
        DStmt::LocalUpdate(_, _, os, _, _) => if spec_objs_down(os) { Some(l) } else { None },
        DStmt::If(_, a, b) => match spec_down_line(*a) {
            Some(x) => Some(x),
            None => spec_down_line(*b),
        },
        DStmt::While(_, _, _, b) => spec_down_line(*b),
        DStmt::For(i, _, _, _, _, b, st, _) => match spec_stmt_down(*i, l) {
            Some(x) => Some(x),
            None => match spec_down_line(*b) {
                Some(x) => Some(x),
                None => spec_stmt_down(*st, l),
            },
        },
        DStmt::Match(_, _, cs) => spec_cases_down(*cs),
        DStmt::Pre(cs, st) => if spec_calls_down(cs) { Some(l) } else { spec_stmt_down(*st, l) },
        DStmt::Moved(st, _) => spec_stmt_down(*st, l),
        DStmt::Gone(st, _, _) => spec_stmt_down(*st, l),
        DStmt::Block(b) => spec_down_line(*b),
        DStmt::Scope(b) => spec_down_line(*b),
        DStmt::Dtors(b) => spec_down_line(*b),
        DStmt::Return(_) => None,
        DStmt::Local(_, _, _) => None,
        DStmt::LocalCall(_, _, _, _) => None,
        DStmt::ReturnCall(_, _) => None,
        DStmt::Assign(_, _) => None,
        DStmt::AssignCall(_, _, _) => None,
        DStmt::SetField(_, _) => None,
        DStmt::SetOut(_, _) => None,
        DStmt::SetOutField(_, _, _) => None,
        DStmt::SetOwnField(_, _, _) => None,
        DStmt::SetThroughField(_, _, _) => None,
        DStmt::CallStmt(_, _) => None,
        DStmt::Exit => None,
        DStmt::Assert(_) => None,
        DStmt::Apply(_, _) => None,
        DStmt::Sort(_, _) => None,
        DStmt::SortBy(_, _, _, _, _) => None,
        DStmt::DeclTemp(_, _) => None,
        DStmt::AssignTemp(_, _) => None,
        DStmt::SetResult(_) => None,
    }
}

/// The model of a function in a file whose interfaces are `ok` when each has a final class over it. When one has none, a method that
/// writes a local back through its interface is refused at the line of that call, decision 0217.
pub open spec fn spec_backed_model(m: Model, ok: bool) -> Model {
    if ok {
        m
    } else {
        match m {
            Model::Full(f) => match spec_down_line(f.body) {
                Some(l) => Model::Bare(f.name, f.params, f.ret, Refusal::Unbacked(l)),
                None => Model::Full(f),
            },
            _ => m,
        }
    }
}

pub open spec fn spec_backed_models(ms: Models, ok: bool) -> Models
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons(m, rest) => List::Cons(spec_backed_model(m, ok), Box::new(spec_backed_models(*rest, ok))),
    }
}

/// No method of `ms` writes a local back through its interface.
pub open spec fn spec_no_down(ms: Models) -> bool
    decreases ms,
{
    match ms {
        List::Nil => true,
        List::Cons(m, rest) => (match m {
            Model::Full(f) => spec_down_line(f.body) is None,
            _ => true,
        }) && spec_no_down(*rest),
    }
}

/// In a file with an interface that no final class backs, no method writes a local back through its interface, decision 0217. In a
/// file where each one has one, the models stay as they are.
pub proof fn lemma_backed_models(ms: Models, ok: bool)
    ensures
        !ok ==> spec_no_down(spec_backed_models(ms, ok)),
        ok ==> spec_backed_models(ms, ok) == ms,
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons(m, rest) => lemma_backed_models(*rest, ok),
    }
}

/// The check of 0217 keeps a method for each key, so each call in a method still names a method of the model, `lemma_calls_resolve`.
pub proof fn lemma_backed_keeps_methods(ms: Models, ok: bool, key: u32)
    ensures
        has_method(spec_backed_models(ms, ok), key) == has_method(ms, key),
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons(m, rest) => lemma_backed_keeps_methods(*rest, ok, key),
    }
}


// ------------------------------------------------------------------ a call through an interface that can come back, decision 0218

/// The pairs of the key of a function of an interface and the key of an override of it in the file.
pub type Pairs = List<(u32, u32)>;

pub open spec fn spec_pairs_of(os: DOverrides) -> Pairs
    decreases os,
{
    match os {
        List::Nil => List::Nil,
        List::Cons(o, rest) => List::Cons((o.base, o.derived), Box::new(spec_pairs_of(*rest))),
    }
}

/// The pairs of each upcast of the file. An upcast that is refused gives none, and its refusal stops the proof of the file.
pub open spec fn spec_pairs(ups: List<Result<DUpcast, Refusal>>) -> Pairs
    decreases ups,
{
    match ups {
        List::Nil => List::Nil,
        List::Cons(u, rest) => match u {
            Ok(up) => spec_append(spec_pairs_of(up.overrides), spec_pairs(*rest)),
            Err(_) => spec_pairs(*rest),
        },
    }
}

/// The destructors of the structs `rows` of the table `sd`.
pub open spec fn spec_dtors(rows: Structs, sd: Structs) -> Names
    decreases rows,
{
    match rows {
        List::Nil => List::Nil,
        List::Cons((k, _), rest) => match spec_member(sd, k, DTOR_NAME) {
            Some((key, _)) => List::Cons(key, Box::new(spec_dtors(*rest, sd))),
            None => spec_dtors(*rest, sd),
        },
    }
}

/// The overrides in the file of the function `k` of an interface.
pub open spec fn spec_overs(prs: Pairs, k: u32) -> Names
    decreases prs,
{
    match prs {
        List::Nil => List::Nil,
        List::Cons((b, d), rest) => if b == k {
            List::Cons(d, Box::new(spec_overs(*rest, k)))
        } else {
            spec_overs(*rest, k)
        },
    }
}

/// The functions that the calls `cs` can run first: each callee, and each override of it.
pub open spec fn spec_succ_calls(cs: List<(u32, bool, u32)>, prs: Pairs) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, _, _), rest) => List::Cons(k, Box::new(spec_append(spec_overs(prs, k), spec_succ_calls(*rest, prs)))),
    }
}

/// The same, less the overrides of each call whose object is owned by `this`: the steps that are no step down the tree of owned
/// objects.
pub open spec fn spec_succ_flat_calls(cs: List<(u32, bool, u32)>, prs: Pairs) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, down, _), rest) => if down {
            List::Cons(k, Box::new(spec_succ_flat_calls(*rest, prs)))
        } else {
            List::Cons(k, Box::new(spec_append(spec_overs(prs, k), spec_succ_flat_calls(*rest, prs))))
        },
    }
}

/// The edges of the call graph from the function `k`: the functions that its body can run first, and each destructor `ds` of the
/// file, which a body runs at the end of a scope. `flat` leaves out the steps down the tree of owned objects.
pub open spec fn spec_succ(all: Fns, prs: Pairs, ds: Names, flat: bool, k: u32) -> Names {
    match spec_find(all, k) {
        Some(f) => spec_append(
            if flat { spec_succ_flat_calls(spec_ocalls_stmts(f.body), prs) } else { spec_succ_calls(spec_ocalls_stmts(f.body), prs) },
            ds,
        ),
        None => List::Nil,
    }
}

pub open spec fn spec_succs(all: Fns, prs: Pairs, ds: Names, flat: bool, ks: Names) -> Names
    decreases ks,
{
    match ks {
        List::Nil => List::Nil,
        List::Cons(k, rest) => spec_append(spec_succ(all, prs, ds, flat, k), spec_succs(all, prs, ds, flat, *rest)),
    }
}

/// Some key of `xs` is not in `r`.
pub open spec fn spec_new(r: Names, xs: Names) -> bool
    decreases xs,
{
    match xs {
        List::Nil => false,
        List::Cons(x, rest) => !spec_has(r, x) || spec_new(r, *rest),
    }
}

/// `r` with each key of `xs` that it does not hold.
pub open spec fn spec_add(r: Names, xs: Names) -> Names
    decreases xs,
{
    match xs {
        List::Nil => r,
        List::Cons(x, rest) => if spec_has(r, x) {
            spec_add(r, *rest)
        } else {
            spec_add(List::Cons(x, Box::new(r)), *rest)
        },
    }
}

/// The functions that a path from `r` reaches, when the steps end in `fuel` steps. `None` when they do not.
pub open spec fn spec_close(all: Fns, prs: Pairs, ds: Names, r: Names, fuel: u64) -> Option<Names>
    decreases fuel,
{
    let next = spec_succs(all, prs, ds, false, r);
    if !spec_new(r, next) {
        Some(r)
    } else if fuel == 0 {
        None
    } else {
        spec_close(all, prs, ds, spec_add(r, next), (fuel - 1) as u64)
    }
}

/// A path of at most `n` edges goes from `from` to `to`.
pub open spec fn spec_reach(all: Fns, prs: Pairs, ds: Names, from: u32, to: u32, n: nat) -> bool
    decreases n,
{
    from == to || (n > 0 && exists|s: u32| #[trigger] spec_has(spec_succ(all, prs, ds, false, from), s) && spec_reach(all, prs, ds, s, to, (n - 1) as nat))
}

/// A path of at most `n` edges goes from `from` to `to`, with at least one edge that is no step down the tree of owned objects.
pub open spec fn spec_reach_flat(all: Fns, prs: Pairs, ds: Names, from: u32, to: u32, n: nat) -> bool
    decreases n,
{
    n > 0 && exists|s: u32|
        (#[trigger] spec_has(spec_succ(all, prs, ds, true, from), s) && spec_reach(all, prs, ds, s, to, (n - 1) as nat))
            || (spec_has(spec_succ(all, prs, ds, false, from), s) && spec_reach_flat(all, prs, ds, s, to, (n - 1) as nat))
}

/// A path from the override `d` can come back to `g`. For a call whose object is owned by `this`, only a path with a step that is
/// no step down counts, since a path of steps down ends. When the steps do not end, the core takes it that a path comes back.
pub open spec fn spec_comes_back(d: u32, g: u32, down: bool, all: Fns, prs: Pairs, ds: Names, fuel: u64) -> bool {
    match spec_close(all, prs, ds, List::Cons(d, Box::new(List::Nil)), fuel) {
        None => true,
        Some(c) => if !down {
            spec_has(c, g)
        } else {
            match spec_close(all, prs, ds, spec_succs(all, prs, ds, true, c), fuel) {
                None => true,
                Some(c2) => spec_has(c2, g),
            }
        },
    }
}

/// An override among `os` can come back to `g`.
pub open spec fn spec_loops_over(os: Names, g: u32, down: bool, all: Fns, prs: Pairs, ds: Names, fuel: u64) -> bool
    decreases os,
{
    match os {
        List::Nil => false,
        List::Cons(d, rest) => spec_comes_back(d, g, down, all, prs, ds, fuel) || spec_loops_over(*rest, g, down, all, prs, ds, fuel),
    }
}

/// The first call among `cs` of the function `g` that can come back to `g` through an override of its callee, by the key of the
/// callee and the line.
pub open spec fn spec_loop_calls(cs: List<(u32, bool, u32)>, g: u32, all: Fns, prs: Pairs, ds: Names, fuel: u64) -> Option<(u32, u32)>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, down, l), rest) => if spec_loops_over(spec_overs(prs, k), g, down, all, prs, ds, fuel) {
            Some((k, l))
        } else {
            spec_loop_calls(*rest, g, all, prs, ds, fuel)
        },
    }
}

/// No override among `os` has a path back to `g`. For a call whose object is owned by `this`, no such path has a step that is no
/// step down.
pub open spec fn spec_safe_over(os: Names, g: u32, down: bool, all: Fns, prs: Pairs, ds: Names) -> bool
    decreases os,
{
    match os {
        List::Nil => true,
        List::Cons(d, rest) => (if down {
            forall|n: nat| !#[trigger] spec_reach_flat(all, prs, ds, d, g, n)
        } else {
            forall|n: nat| !#[trigger] spec_reach(all, prs, ds, d, g, n)
        }) && spec_safe_over(*rest, g, down, all, prs, ds),
    }
}

/// No call among `cs` of `g` can come back to `g` through an override of its callee, other than down the tree of owned objects.
pub open spec fn spec_safe_calls(cs: List<(u32, bool, u32)>, g: u32, all: Fns, prs: Pairs, ds: Names) -> bool
    decreases cs,
{
    match cs {
        List::Nil => true,
        List::Cons((k, down, _), rest) => spec_safe_over(spec_overs(prs, k), g, down, all, prs, ds) && spec_safe_calls(*rest, g, all, prs, ds),
    }
}

pub proof fn lemma_has_append(a: Names, b: Names, x: u32)
    ensures
        spec_has(spec_append(a, b), x) == (spec_has(a, x) || spec_has(b, x)),
    decreases a,
{
    match a {
        List::Nil => {},
        List::Cons(_, rest) => lemma_has_append(*rest, b, x),
    }
}

pub proof fn lemma_not_new(r: Names, xs: Names, x: u32)
    ensures
        !spec_new(r, xs) && spec_has(xs, x) ==> spec_has(r, x),
    decreases xs,
{
    match xs {
        List::Nil => {},
        List::Cons(_, rest) => lemma_not_new(r, *rest, x),
    }
}

pub proof fn lemma_add_keeps(r: Names, xs: Names, x: u32)
    ensures
        spec_has(r, x) ==> spec_has(spec_add(r, xs), x),
    decreases xs,
{
    match xs {
        List::Nil => {},
        List::Cons(y, rest) => if spec_has(r, y) {
            lemma_add_keeps(r, *rest, x);
        } else {
            lemma_add_keeps(List::Cons(y, Box::new(r)), *rest, x);
        },
    }
}

pub proof fn lemma_succs_has(all: Fns, prs: Pairs, ds: Names, flat: bool, ks: Names, k: u32, s: u32)
    ensures
        spec_has(ks, k) && spec_has(spec_succ(all, prs, ds, flat, k), s) ==> spec_has(spec_succs(all, prs, ds, flat, ks), s),
    decreases ks,
{
    match ks {
        List::Nil => {},
        List::Cons(j, rest) => {
            lemma_has_append(spec_succ(all, prs, ds, flat, j), spec_succs(all, prs, ds, flat, *rest), s);
            lemma_succs_has(all, prs, ds, flat, *rest, k, s);
        },
    }
}

/// The result of the steps holds each key of the start, and no step from it adds a key.
pub proof fn lemma_close(all: Fns, prs: Pairs, ds: Names, r: Names, fuel: u64, x: u32)
    ensures
        spec_close(all, prs, ds, r, fuel) is Some ==> !spec_new(spec_close(all, prs, ds, r, fuel)->Some_0, spec_succs(all, prs, ds, false, spec_close(all, prs, ds, r, fuel)->Some_0)),
        spec_close(all, prs, ds, r, fuel) is Some && spec_has(r, x) ==> spec_has(spec_close(all, prs, ds, r, fuel)->Some_0, x),
    decreases fuel,
{
    let next = spec_succs(all, prs, ds, false, r);
    if spec_new(r, next) && fuel > 0 {
        lemma_add_keeps(r, next, x);
        lemma_close(all, prs, ds, spec_add(r, next), (fuel - 1) as u64, x);
    }
}

/// A set of keys that no step leaves holds each key that a path from one of its keys reaches.
pub proof fn lemma_reach_closed(all: Fns, prs: Pairs, ds: Names, c: Names, from: u32, to: u32, n: nat)
    requires
        !spec_new(c, spec_succs(all, prs, ds, false, c)),
        spec_has(c, from),
        spec_reach(all, prs, ds, from, to, n),
    ensures
        spec_has(c, to),
    decreases n,
{
    if from != to {
        let s = choose|s: u32| #[trigger] spec_has(spec_succ(all, prs, ds, false, from), s) && spec_reach(all, prs, ds, s, to, (n - 1) as nat);
        lemma_succs_has(all, prs, ds, false, c, from, s);
        lemma_not_new(c, spec_succs(all, prs, ds, false, c), s);
        lemma_reach_closed(all, prs, ds, c, s, to, (n - 1) as nat);
    }
}

/// A path with a step that is no step down, from a key of a closed set `c`, ends in the closed set `c2` that holds each such step
/// from `c`.
pub proof fn lemma_reach_flat_closed(all: Fns, prs: Pairs, ds: Names, c: Names, c2: Names, from: u32, to: u32, n: nat)
    requires
        !spec_new(c, spec_succs(all, prs, ds, false, c)),
        !spec_new(c2, spec_succs(all, prs, ds, false, c2)),
        forall|x: u32| #[trigger] spec_has(spec_succs(all, prs, ds, true, c), x) ==> spec_has(c2, x),
        spec_has(c, from),
        spec_reach_flat(all, prs, ds, from, to, n),
    ensures
        spec_has(c2, to),
    decreases n,
{
    let s = choose|s: u32|
        (#[trigger] spec_has(spec_succ(all, prs, ds, true, from), s) && spec_reach(all, prs, ds, s, to, (n - 1) as nat))
            || (spec_has(spec_succ(all, prs, ds, false, from), s) && spec_reach_flat(all, prs, ds, s, to, (n - 1) as nat));
    if spec_has(spec_succ(all, prs, ds, true, from), s) && spec_reach(all, prs, ds, s, to, (n - 1) as nat) {
        lemma_succs_has(all, prs, ds, true, c, from, s);
        lemma_reach_closed(all, prs, ds, c2, s, to, (n - 1) as nat);
    } else {
        lemma_succs_has(all, prs, ds, false, c, from, s);
        lemma_not_new(c, spec_succs(all, prs, ds, false, c), s);
        lemma_reach_flat_closed(all, prs, ds, c, c2, s, to, (n - 1) as nat);
    }
}

pub proof fn lemma_comes_back(d: u32, g: u32, down: bool, all: Fns, prs: Pairs, ds: Names, fuel: u64)
    ensures
        !spec_comes_back(d, g, down, all, prs, ds, fuel) ==> (if down {
            forall|n: nat| !#[trigger] spec_reach_flat(all, prs, ds, d, g, n)
        } else {
            forall|n: nat| !#[trigger] spec_reach(all, prs, ds, d, g, n)
        }),
{
    let start = List::Cons(d, Box::new(List::Nil));
    if !spec_comes_back(d, g, down, all, prs, ds, fuel) {
        lemma_close(all, prs, ds, start, fuel, d);
        let c = spec_close(all, prs, ds, start, fuel)->Some_0;
        if !down {
            assert forall|n: nat| !#[trigger] spec_reach(all, prs, ds, d, g, n) by {
                if spec_reach(all, prs, ds, d, g, n) {
                    lemma_reach_closed(all, prs, ds, c, d, g, n);
                }
            }
        } else {
            let flat = spec_succs(all, prs, ds, true, c);
            let c2 = spec_close(all, prs, ds, flat, fuel)->Some_0;
            assert forall|x: u32| #[trigger] spec_has(flat, x) implies spec_has(c2, x) by {
                lemma_close(all, prs, ds, flat, fuel, x);
            }
            lemma_close(all, prs, ds, flat, fuel, d);
            assert forall|n: nat| !#[trigger] spec_reach_flat(all, prs, ds, d, g, n) by {
                if spec_reach_flat(all, prs, ds, d, g, n) {
                    lemma_reach_flat_closed(all, prs, ds, c, c2, d, g, n);
                }
            }
        }
    }
}

pub proof fn lemma_safe_over(os: Names, g: u32, down: bool, all: Fns, prs: Pairs, ds: Names, fuel: u64)
    ensures
        !spec_loops_over(os, g, down, all, prs, ds, fuel) ==> spec_safe_over(os, g, down, all, prs, ds),
    decreases os,
{
    match os {
        List::Nil => {},
        List::Cons(d, rest) => {
            lemma_safe_over(*rest, g, down, all, prs, ds, fuel);
            lemma_comes_back(d, g, down, all, prs, ds, fuel);
        },
    }
}

/// A call that the check keeps cannot come back to its function through an override of its callee on a path of any length, other
/// than down the tree of owned objects.
pub proof fn lemma_safe_calls(cs: List<(u32, bool, u32)>, g: u32, all: Fns, prs: Pairs, ds: Names, fuel: u64)
    ensures
        spec_loop_calls(cs, g, all, prs, ds, fuel) is None ==> spec_safe_calls(cs, g, all, prs, ds),
    decreases cs,
{
    match cs {
        List::Nil => {},
        List::Cons((k, down, _), rest) => {
            lemma_safe_over(spec_overs(prs, k), g, down, all, prs, ds, fuel);
            lemma_safe_calls(*rest, g, all, prs, ds, fuel);
        },
    }
}

/// The model of the function `f`: a method with a call that can come back is refused at the line of that call, decision 0218.
pub open spec fn spec_loop_model(m: Model, f: Function, all: Fns, prs: Pairs, ds: Names, fuel: u64) -> Model {
    match m {
        Model::Full(meth) => match spec_loop_calls(spec_ocalls_stmts(f.body), f.name, all, prs, ds, fuel) {
            Some((k, l)) => Model::Bare(meth.name, meth.params, meth.ret, Refusal::Loop(k, l)),
            None => Model::Full(meth),
        },
        _ => m,
    }
}

/// The models `ms` of the functions `fs`, in their order, with the check of 0218.
pub open spec fn spec_loop_models(ms: Models, fs: Fns, all: Fns, prs: Pairs, ds: Names, fuel: u64) -> Models
    decreases ms,
{
    match (ms, fs) {
        (List::Cons(m, mrest), List::Cons(f, frest)) => List::Cons(spec_loop_model(m, *f, all, prs, ds, fuel), Box::new(spec_loop_models(*mrest, *frest, all, prs, ds, fuel))),
        _ => ms,
    }
}

/// Each method of `ms` is the model of the function of `fs` at its place, and no call in its body can come back to it.
pub open spec fn spec_no_loop(ms: Models, fs: Fns, all: Fns, prs: Pairs, ds: Names) -> bool
    decreases ms,
{
    match (ms, fs) {
        (List::Cons(m, mrest), List::Cons(f, frest)) => (match m {
            Model::Full(_) => spec_safe_calls(spec_ocalls_stmts(f.body), f.name, all, prs, ds),
            _ => true,
        }) && spec_no_loop(*mrest, *frest, all, prs, ds),
        (List::Nil, _) => true,
        _ => false,
    }
}

/// The count of the functions of the file and one more, the limit of the steps of 0218.
pub open spec fn spec_fuel(fs: Fns) -> u64
    decreases fs,
{
    match fs {
        List::Nil => 1,
        List::Cons(_, rest) => if spec_fuel(*rest) < u64::MAX { (spec_fuel(*rest) + 1) as u64 } else { u64::MAX },
    }
}

pub proof fn lemma_loop_models(ms: Models, fs: Fns, all: Fns, prs: Pairs, ds: Names, fuel: u64)
    requires
        spec_len_le(ms, fs),
    ensures
        spec_no_loop(spec_loop_models(ms, fs, all, prs, ds, fuel), fs, all, prs, ds),
        forall|k: u32| #[trigger] has_method(spec_loop_models(ms, fs, all, prs, ds, fuel), k) == has_method(ms, k),
    decreases ms,
{
    match (ms, fs) {
        (List::Cons(m, mrest), List::Cons(f, frest)) => {
            lemma_loop_models(*mrest, *frest, all, prs, ds, fuel);
            lemma_safe_calls(spec_ocalls_stmts(f.body), f.name, all, prs, ds, fuel);
            assert forall|k: u32| #[trigger] has_method(spec_loop_models(ms, fs, all, prs, ds, fuel), k) == has_method(ms, k) by {
                assert(has_method(spec_loop_models(*mrest, *frest, all, prs, ds, fuel), k) == has_method(*mrest, k));
            }
        },
        _ => {},
    }
}

/// `ms` has no more items than `fs`.
pub open spec fn spec_len_le(ms: Models, fs: Fns) -> bool
    decreases ms,
{
    match (ms, fs) {
        (List::Nil, _) => true,
        (List::Cons(_, mrest), List::Cons(_, frest)) => spec_len_le(*mrest, *frest),
        _ => false,
    }
}

pub proof fn lemma_unit_len(fs: Fns, all: Fns, sd: Structs)
    ensures
        spec_len_le(spec_unit(fs, all, sd), fs),
    decreases fs,
{
    match fs {
        List::Nil => {},
        List::Cons(_, rest) => lemma_unit_len(*rest, all, sd),
    }
}

pub proof fn lemma_backed_len(ms: Models, fs: Fns, ok: bool)
    requires
        spec_len_le(ms, fs),
    ensures
        spec_len_le(spec_backed_models(ms, ok), fs),
    decreases ms,
{
    match (ms, fs) {
        (List::Cons(_, mrest), List::Cons(_, frest)) => lemma_backed_len(*mrest, *frest, ok),
        _ => {},
    }
}

/// The pairs of interface functions and overrides of a file, and its destructors, under the table of the unit, decision 0218.
pub open spec fn spec_file_pairs(all: Fns, sd: Structs, bases: Bases) -> Pairs {
    spec_pairs(spec_upcasts(bases, all, spec_marked(sd, all)))
}

pub open spec fn spec_file_dtors(all: Fns, sd: Structs) -> Names {
    spec_dtors(spec_marked(sd, all), spec_marked(sd, all))
}

/// The models of the functions of a file, with the checks of 0217 on its classes over interfaces and of 0218 on its calls through
/// an interface.
pub open spec fn spec_file(all: Fns, sd: Structs, bases: Bases) -> Models {
    spec_loop_models(
        spec_backed_models(spec_unit(all, all, spec_marked(sd, all)), spec_backed(all, bases)),
        all,
        all,
        spec_file_pairs(all, sd, bases),
        spec_file_dtors(all, sd),
        spec_fuel(all),
    )
}

} // verus!

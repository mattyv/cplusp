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
                            ensures: spec_ret_len(f.ret, f.line, spec_linked(f, ens, spec_pure_body(f.params, body, all, sd, spec_static_key(sd, f.name)))),
                            decreases: dec,
                            body,
                            function: spec_pure_body(f.params, body, all, sd, spec_static_key(sd, f.name)),
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

/// The model of a struct: each field a type of the subset, decision 0073. A field can be a sequence, decision 0076.
pub open spec fn spec_fields(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        // An optional of a struct is no field yet, decision 0137. A unique_ptr of a struct or an interface is a field, decision 0171.
        List::Cons((n, t), rest) => match (if (t is Opt && t->Opt_0 is Struct) || t is Ptr || (t is Own && !(t->Own_0 is Struct)) || t is F64 { Err(Refusal::Element(line)) } else { spec_ty(t, line) }) {
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

} // verus!

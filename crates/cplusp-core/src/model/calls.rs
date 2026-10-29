//! The translator: the call graph of a file, decision 0218. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ the calls of a body, decision 0218

/// The object of a call is owned by the object of the function that makes it: `f->g()` of a `std::unique_ptr` field `f` of
/// `this`, decision 0219. Such an object is a part of `this`, so a chain of such calls goes down the tree of owned objects and ends.
pub open spec fn spec_down_obj(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Value(a) => match *a {
            Expr::Field(b, _) => match *b {
                Expr::Var(_, t) => t is This || t is ThisMut,
                _ => false,
            },
            _ => false,
        },
        Expr::Cast(c, a) => (c == CastKind::Read || c == CastKind::NoOp) && spec_down_obj(*a),
        Expr::Paren(a) => spec_down_obj(*a),
        _ => false,
    }
}

/// The first argument of a call, its object for a member function, is owned by `this`.
pub open spec fn spec_down_args(args: Args) -> bool {
    match args {
        List::Cons(a, _) => spec_down_obj(*a),
        List::Nil => false,
    }
}

/// The calls of an expression, as the key, whether its object is owned by `this`, and the line of each, decision 0218.
pub open spec fn spec_ocalls(e: Expr) -> List<(u32, bool, u32)>
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => spec_append(spec_ocalls(*f1), spec_ocalls(*f2)),
        Expr::Not(f0) => spec_ocalls(*f0),
        Expr::Neg(f0) => spec_ocalls(*f0),
        Expr::Cast(_, f1) => spec_ocalls(*f1),
        Expr::Paren(f0) => spec_ocalls(*f0),
        Expr::Brace(f0) => spec_ocalls(*f0),
        Expr::Call(k, _, args, at) => List::Cons((k, spec_down_args(*args), at), Box::new(spec_ocalls_args(*args))),
        Expr::Size(f0) => spec_ocalls(*f0),
        Expr::Back(f0) => spec_ocalls(*f0),
        Expr::Either(f0, _) => spec_ocalls(*f0),
        Expr::Index(f0, f1) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Copy(f0, _, _) => spec_ocalls(*f0),
        Expr::Field(f0, _) => spec_ocalls(*f0),
        Expr::Construct(_, f1) => spec_ocalls_args(*f1),
        Expr::Forall(_, f1) => spec_ocalls(*f1),
        Expr::Exists(_, f1) => spec_ocalls(*f1),
        Expr::Chain(_, _, f2, f3, f4) => spec_append(spec_ocalls(*f2), spec_append(spec_ocalls(*f3), spec_ocalls(*f4))),
        Expr::HasValue(f0) => spec_ocalls(*f0),
        Expr::Value(f0) => spec_ocalls(*f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => spec_ocalls(*f0),
        Expr::Empty(f0) => spec_ocalls(*f0),
        Expr::Subspan(f0, f1) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Apply(_, f1) => spec_ocalls_args(*f1),
        Expr::Suffix(f0, f1) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Prefix(f0, f1) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Slice(f0, f1, f2) => spec_append(spec_ocalls(*f0), spec_append(spec_ocalls(*f1), spec_ocalls(*f2))),
        Expr::Divide(_, f1, f2, _) => spec_append(spec_ocalls(*f1), spec_ocalls(*f2)),
        Expr::MApply(f0, _, f2) => spec_append(spec_ocalls(*f0), spec_ocalls_args(*f2)),
        Expr::Old(f0) => spec_ocalls(*f0),
        Expr::Cond(f0, f1, f2) => spec_append(spec_ocalls(*f0), spec_append(spec_ocalls(*f1), spec_ocalls(*f2))),
        Expr::Shr(f0, f1, _) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Bits(_, f1, f2, _) => spec_append(spec_ocalls(*f1), spec_ocalls(*f2)),
        Expr::StaticCast(_, f1) => spec_ocalls(*f1),
        Expr::Holds(_, f1) => spec_ocalls(*f1),
        Expr::GetAlt(_, f1) => spec_ocalls(*f1),
        Expr::List(f0) => spec_ocalls_args(*f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => spec_append(spec_ocalls(*f0), spec_ocalls(*f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => spec_ocalls(*f0),
        Expr::Abs(f0) => spec_ocalls(*f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => spec_append(spec_ocalls(*f0), spec_ocalls(*f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub open spec fn spec_ocalls_args(args: Args) -> List<(u32, bool, u32)>
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_ocalls(*a), spec_ocalls_args(*rest)),
    }
}

pub open spec fn spec_ocalls_stmts(ss: Stmts) -> List<(u32, bool, u32)>
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_ocalls_stmt(*s), spec_ocalls_stmts(*rest)),
    }
}

pub open spec fn spec_ocalls_stmt(s: Stmt) -> List<(u32, bool, u32)>
    decreases s,
{
    match s {
        Stmt::Return(e, _) => spec_ocalls(e),
        Stmt::If(c, t, f, _) => spec_append(spec_ocalls(c), spec_append(spec_ocalls_stmts(*t), spec_ocalls_stmts(*f))),
        Stmt::Local(_, _, e, _) => spec_ocalls(e),
        Stmt::Assign(_, e, _) => spec_ocalls(e),
        Stmt::While(c, _, body, _) => spec_append(spec_ocalls(c), spec_ocalls_stmts(*body)),
        Stmt::For(init, c, step, _, body, _) => spec_append(spec_ocalls_stmt(*init), spec_append(spec_ocalls(c), spec_append(spec_ocalls_stmt(*step), spec_ocalls_stmts(*body)))),
        Stmt::SetField(_, e, _) => spec_ocalls(e),
        Stmt::SetRefField(_, _, e, _) => spec_ocalls(e),
        Stmt::SetOwnField(_, _, e, _) => spec_ocalls(e),
        Stmt::Switch(e, _, cs, _) => spec_append(spec_ocalls(e), spec_ocalls_cases(*cs)),
        Stmt::Call(k, _, args, l) => List::Cons((k, spec_down_args(*args), l), Box::new(spec_ocalls_args(*args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => spec_append(spec_ocalls(sq), spec_ocalls_stmts(*body)),
        Stmt::SetIndex(_, i, e, _) => spec_append(spec_ocalls(i), spec_ocalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => spec_append(spec_ocalls(i), spec_ocalls(e)),
        Stmt::PushField(_, e, _) => spec_ocalls(e),
        Stmt::SetThroughField(_, _, e, _) => spec_ocalls(e),
        Stmt::PushBack(_, e, _) => spec_ocalls(e),
        Stmt::SortBy(_, _, _, _, e, _) => spec_ocalls(e),
        Stmt::Block(b, _) => spec_ocalls_stmts(*b),
        _ => List::Nil,
    }
}

pub open spec fn spec_ocalls_cases(cs: Cases) -> List<(u32, bool, u32)>
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_ocalls_stmts(*body), spec_ocalls_cases(*rest)),
    }
}

pub fn down_obj(e: &Expr) -> (r: bool)
    ensures
        r == spec_down_obj(*e),
    decreases e,
{
    match e {
        Expr::Value(a) => match &**a {
            Expr::Field(b, _) => match &**b {
                Expr::Var(_, t) => matches!(t, Ty::This(_)) || matches!(t, Ty::ThisMut(_)),
                _ => false,
            },
            _ => false,
        },
        Expr::Cast(c, a) => (*c == CastKind::Read || *c == CastKind::NoOp) && down_obj(a),
        Expr::Paren(a) => down_obj(a),
        _ => false,
    }
}

pub fn down_args(args: &Args) -> (r: bool)
    ensures
        r == spec_down_args(*args),
{
    match args {
        List::Cons(a, _) => down_obj(a),
        List::Nil => false,
    }
}

pub fn ocalls(e: &Expr) -> (r: List<(u32, bool, u32)>)
    ensures
        r == spec_ocalls(*e),
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => append(ocalls(f1), ocalls(f2)),
        Expr::Not(f0) => ocalls(f0),
        Expr::Neg(f0) => ocalls(f0),
        Expr::Cast(_, f1) => ocalls(f1),
        Expr::Paren(f0) => ocalls(f0),
        Expr::Brace(f0) => ocalls(f0),
        Expr::Call(k, _, args, at) => List::Cons((*k, down_args(args), *at), Box::new(ocalls_args(args))),
        Expr::Size(f0) => ocalls(f0),
        Expr::Back(f0) => ocalls(f0),
        Expr::Either(f0, _) => ocalls(f0),
        Expr::Index(f0, f1) => append(ocalls(f0), ocalls(f1)),
        Expr::Copy(f0, _, _) => ocalls(f0),
        Expr::Field(f0, _) => ocalls(f0),
        Expr::Construct(_, f1) => ocalls_args(f1),
        Expr::Forall(_, f1) => ocalls(f1),
        Expr::Exists(_, f1) => ocalls(f1),
        Expr::Chain(_, _, f2, f3, f4) => append(ocalls(f2), append(ocalls(f3), ocalls(f4))),
        Expr::HasValue(f0) => ocalls(f0),
        Expr::Value(f0) => ocalls(f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => ocalls(f0),
        Expr::Empty(f0) => ocalls(f0),
        Expr::Subspan(f0, f1) => append(ocalls(f0), ocalls(f1)),
        Expr::Apply(_, f1) => ocalls_args(f1),
        Expr::Suffix(f0, f1) => append(ocalls(f0), ocalls(f1)),
        Expr::Prefix(f0, f1) => append(ocalls(f0), ocalls(f1)),
        Expr::Slice(f0, f1, f2) => append(ocalls(f0), append(ocalls(f1), ocalls(f2))),
        Expr::Divide(_, f1, f2, _) => append(ocalls(f1), ocalls(f2)),
        Expr::MApply(f0, _, f2) => append(ocalls(f0), ocalls_args(f2)),
        Expr::Old(f0) => ocalls(f0),
        Expr::Cond(f0, f1, f2) => append(ocalls(f0), append(ocalls(f1), ocalls(f2))),
        Expr::Shr(f0, f1, _) => append(ocalls(f0), ocalls(f1)),
        Expr::Bits(_, f1, f2, _) => append(ocalls(f1), ocalls(f2)),
        Expr::StaticCast(_, f1) => ocalls(f1),
        Expr::Holds(_, f1) => ocalls(f1),
        Expr::GetAlt(_, f1) => ocalls(f1),
        Expr::List(f0) => ocalls_args(f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => append(ocalls(f0), ocalls(f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => ocalls(f0),
        Expr::Abs(f0) => ocalls(f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => append(ocalls(f0), ocalls(f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub fn ocalls_args(args: &Args) -> (r: List<(u32, bool, u32)>)
    ensures
        r == spec_ocalls_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(ocalls(a), ocalls_args(rest)),
    }
}

pub fn ocalls_stmts(ss: &Stmts) -> (r: List<(u32, bool, u32)>)
    ensures
        r == spec_ocalls_stmts(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(ocalls_stmt(s), ocalls_stmts(rest)),
    }
}

pub fn ocalls_stmt(s: &Stmt) -> (r: List<(u32, bool, u32)>)
    ensures
        r == spec_ocalls_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Return(e, _) => ocalls(e),
        Stmt::If(c, t, f, _) => append(ocalls(c), append(ocalls_stmts(t), ocalls_stmts(f))),
        Stmt::Local(_, _, e, _) => ocalls(e),
        Stmt::Assign(_, e, _) => ocalls(e),
        Stmt::While(c, _, body, _) => append(ocalls(c), ocalls_stmts(body)),
        Stmt::For(init, c, step, _, body, _) => append(ocalls_stmt(init), append(ocalls(c), append(ocalls_stmt(step), ocalls_stmts(body)))),
        Stmt::SetField(_, e, _) => ocalls(e),
        Stmt::SetRefField(_, _, e, _) => ocalls(e),
        Stmt::SetOwnField(_, _, e, _) => ocalls(e),
        Stmt::Switch(e, _, cs, _) => append(ocalls(e), ocalls_cases(cs)),
        Stmt::Call(k, _, args, l) => List::Cons((*k, down_args(args), *l), Box::new(ocalls_args(args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => append(ocalls(sq), ocalls_stmts(body)),
        Stmt::SetIndex(_, i, e, _) => append(ocalls(i), ocalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => append(ocalls(i), ocalls(e)),
        Stmt::PushField(_, e, _) => ocalls(e),
        Stmt::SetThroughField(_, _, e, _) => ocalls(e),
        Stmt::PushBack(_, e, _) => ocalls(e),
        Stmt::SortBy(_, _, _, _, e, _) => ocalls(e),
        Stmt::Block(b, _) => ocalls_stmts(b),
        _ => List::Nil,
    }
}

pub fn ocalls_cases(cs: &Cases) -> (r: List<(u32, bool, u32)>)
    ensures
        r == spec_ocalls_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(ocalls_stmts(body), ocalls_cases(rest)),
    }
}

} // verus!

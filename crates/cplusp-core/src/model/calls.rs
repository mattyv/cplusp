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


// ------------------------------------------------------------------ the structs that a body makes, decision 0222

/// The keys of the structs that an expression makes as a value, at any depth, decision 0222.
pub open spec fn spec_made(e: Expr) -> List<u32>
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => spec_append(spec_made(*f1), spec_made(*f2)),
        Expr::Not(f0) => spec_made(*f0),
        Expr::Neg(f0) => spec_made(*f0),
        Expr::Cast(_, f1) => spec_made(*f1),
        Expr::Paren(f0) => spec_made(*f0),
        Expr::Brace(f0) => spec_made(*f0),
        Expr::Call(_, _, args, _) => spec_made_args(*args),
        Expr::Size(f0) => spec_made(*f0),
        Expr::Back(f0) => spec_made(*f0),
        Expr::Either(f0, _) => spec_made(*f0),
        Expr::Index(f0, f1) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Copy(f0, _, _) => spec_made(*f0),
        Expr::Field(f0, _) => spec_made(*f0),
        Expr::Construct(k, f1) => List::Cons(k, Box::new(spec_made_args(*f1))),
        Expr::Forall(_, f1) => spec_made(*f1),
        Expr::Exists(_, f1) => spec_made(*f1),
        Expr::Chain(_, _, f2, f3, f4) => spec_append(spec_made(*f2), spec_append(spec_made(*f3), spec_made(*f4))),
        Expr::HasValue(f0) => spec_made(*f0),
        Expr::Value(f0) => spec_made(*f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => spec_made(*f0),
        Expr::Empty(f0) => spec_made(*f0),
        Expr::Subspan(f0, f1) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Apply(_, f1) => spec_made_args(*f1),
        Expr::Suffix(f0, f1) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Prefix(f0, f1) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Slice(f0, f1, f2) => spec_append(spec_made(*f0), spec_append(spec_made(*f1), spec_made(*f2))),
        Expr::Divide(_, f1, f2, _) => spec_append(spec_made(*f1), spec_made(*f2)),
        Expr::MApply(f0, _, f2) => spec_append(spec_made(*f0), spec_made_args(*f2)),
        Expr::Old(f0) => spec_made(*f0),
        Expr::Cond(f0, f1, f2) => spec_append(spec_made(*f0), spec_append(spec_made(*f1), spec_made(*f2))),
        Expr::Shr(f0, f1, _) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Bits(_, f1, f2, _) => spec_append(spec_made(*f1), spec_made(*f2)),
        Expr::StaticCast(_, f1) => spec_made(*f1),
        Expr::Holds(_, f1) => spec_made(*f1),
        Expr::GetAlt(_, f1) => spec_made(*f1),
        Expr::List(f0) => spec_made_args(*f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => spec_append(spec_made(*f0), spec_made(*f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => spec_made(*f0),
        Expr::Abs(f0) => spec_made(*f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => spec_append(spec_made(*f0), spec_made(*f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub open spec fn spec_made_args(args: Args) -> List<u32>
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_made(*a), spec_made_args(*rest)),
    }
}

pub open spec fn spec_made_stmts(ss: Stmts) -> List<u32>
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_made_stmt(*s), spec_made_stmts(*rest)),
    }
}

pub open spec fn spec_made_stmt(s: Stmt) -> List<u32>
    decreases s,
{
    match s {
        Stmt::Return(e, _) => spec_made(e),
        Stmt::If(c, t, f, _) => spec_append(spec_made(c), spec_append(spec_made_stmts(*t), spec_made_stmts(*f))),
        Stmt::Local(_, _, e, _) => spec_made(e),
        Stmt::Assign(_, e, _) => spec_made(e),
        Stmt::While(c, _, body, _) => spec_append(spec_made(c), spec_made_stmts(*body)),
        Stmt::For(init, c, step, _, body, _) => spec_append(spec_made_stmt(*init), spec_append(spec_made(c), spec_append(spec_made_stmt(*step), spec_made_stmts(*body)))),
        Stmt::SetField(_, e, _) => spec_made(e),
        Stmt::SetRefField(_, _, e, _) => spec_made(e),
        Stmt::SetOwnField(_, _, e, _) => spec_made(e),
        Stmt::Switch(e, _, cs, _) => spec_append(spec_made(e), spec_made_cases(*cs)),
        Stmt::Call(_, _, args, _) => spec_made_args(*args),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => spec_append(spec_made(sq), spec_made_stmts(*body)),
        Stmt::SetIndex(_, i, e, _) => spec_append(spec_made(i), spec_made(e)),
        Stmt::SetFieldAt(_, i, e, _) => spec_append(spec_made(i), spec_made(e)),
        Stmt::PushField(_, e, _) => spec_made(e),
        Stmt::SetThroughField(_, _, e, _) => spec_made(e),
        Stmt::PushBack(_, e, _) => spec_made(e),
        Stmt::SortBy(_, _, _, _, e, _) => spec_made(e),
        Stmt::Block(b, _) => spec_made_stmts(*b),
        _ => List::Nil,
    }
}

pub open spec fn spec_made_cases(cs: Cases) -> List<u32>
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_made_stmts(*body), spec_made_cases(*rest)),
    }
}

pub fn made(e: &Expr) -> (r: List<u32>)
    ensures
        r == spec_made(*e),
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => append(made(f1), made(f2)),
        Expr::Not(f0) => made(f0),
        Expr::Neg(f0) => made(f0),
        Expr::Cast(_, f1) => made(f1),
        Expr::Paren(f0) => made(f0),
        Expr::Brace(f0) => made(f0),
        Expr::Call(_, _, args, _) => made_args(args),
        Expr::Size(f0) => made(f0),
        Expr::Back(f0) => made(f0),
        Expr::Either(f0, _) => made(f0),
        Expr::Index(f0, f1) => append(made(f0), made(f1)),
        Expr::Copy(f0, _, _) => made(f0),
        Expr::Field(f0, _) => made(f0),
        Expr::Construct(k, f1) => List::Cons(*k, Box::new(made_args(f1))),
        Expr::Forall(_, f1) => made(f1),
        Expr::Exists(_, f1) => made(f1),
        Expr::Chain(_, _, f2, f3, f4) => append(made(f2), append(made(f3), made(f4))),
        Expr::HasValue(f0) => made(f0),
        Expr::Value(f0) => made(f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => made(f0),
        Expr::Empty(f0) => made(f0),
        Expr::Subspan(f0, f1) => append(made(f0), made(f1)),
        Expr::Apply(_, f1) => made_args(f1),
        Expr::Suffix(f0, f1) => append(made(f0), made(f1)),
        Expr::Prefix(f0, f1) => append(made(f0), made(f1)),
        Expr::Slice(f0, f1, f2) => append(made(f0), append(made(f1), made(f2))),
        Expr::Divide(_, f1, f2, _) => append(made(f1), made(f2)),
        Expr::MApply(f0, _, f2) => append(made(f0), made_args(f2)),
        Expr::Old(f0) => made(f0),
        Expr::Cond(f0, f1, f2) => append(made(f0), append(made(f1), made(f2))),
        Expr::Shr(f0, f1, _) => append(made(f0), made(f1)),
        Expr::Bits(_, f1, f2, _) => append(made(f1), made(f2)),
        Expr::StaticCast(_, f1) => made(f1),
        Expr::Holds(_, f1) => made(f1),
        Expr::GetAlt(_, f1) => made(f1),
        Expr::List(f0) => made_args(f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => append(made(f0), made(f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => made(f0),
        Expr::Abs(f0) => made(f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => append(made(f0), made(f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub fn made_args(args: &Args) -> (r: List<u32>)
    ensures
        r == spec_made_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(made(a), made_args(rest)),
    }
}

pub fn made_stmts(ss: &Stmts) -> (r: List<u32>)
    ensures
        r == spec_made_stmts(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(made_stmt(s), made_stmts(rest)),
    }
}

pub fn made_stmt(s: &Stmt) -> (r: List<u32>)
    ensures
        r == spec_made_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Return(e, _) => made(e),
        Stmt::If(c, t, f, _) => append(made(c), append(made_stmts(t), made_stmts(f))),
        Stmt::Local(_, _, e, _) => made(e),
        Stmt::Assign(_, e, _) => made(e),
        Stmt::While(c, _, body, _) => append(made(c), made_stmts(body)),
        Stmt::For(init, c, step, _, body, _) => append(made_stmt(init), append(made(c), append(made_stmt(step), made_stmts(body)))),
        Stmt::SetField(_, e, _) => made(e),
        Stmt::SetRefField(_, _, e, _) => made(e),
        Stmt::SetOwnField(_, _, e, _) => made(e),
        Stmt::Switch(e, _, cs, _) => append(made(e), made_cases(cs)),
        Stmt::Call(_, _, args, _) => made_args(args),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => append(made(sq), made_stmts(body)),
        Stmt::SetIndex(_, i, e, _) => append(made(i), made(e)),
        Stmt::SetFieldAt(_, i, e, _) => append(made(i), made(e)),
        Stmt::PushField(_, e, _) => made(e),
        Stmt::SetThroughField(_, _, e, _) => made(e),
        Stmt::PushBack(_, e, _) => made(e),
        Stmt::SortBy(_, _, _, _, e, _) => made(e),
        Stmt::Block(b, _) => made_stmts(b),
        _ => List::Nil,
    }
}

pub fn made_cases(cs: &Cases) -> (r: List<u32>)
    ensures
        r == spec_made_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(made_stmts(body), made_cases(rest)),
    }
}


// ------------------------------------------------------------------ a function that ends a life, decision 0222

/// A type of a field that holds no struct and no `std::unique_ptr`.
pub open spec fn spec_flat_scalar(s: Scalar) -> bool {
    !(s is Struct) && !(s is Own)
}

pub open spec fn spec_flat(t: Ty) -> bool {
    match t {
        Ty::I32 | Ty::I64 | Ty::U8 | Ty::U32 | Ty::U64 | Ty::I8 | Ty::I16 | Ty::U16 | Ty::F64 | Ty::Bool | Ty::Enum(_) => true,
        Ty::Seq(s, _) => spec_flat_scalar(s),
        Ty::Vec(s) => spec_flat_scalar(s),
        Ty::Opt(s) => spec_flat_scalar(s),
        Ty::Variant(a, b) => spec_flat_scalar(a) && spec_flat_scalar(b),
        _ => false,
    }
}

pub open spec fn spec_fields_flat(ps: Params) -> bool
    decreases ps,
{
    match ps {
        List::Nil => true,
        List::Cons((_, t), rest) => spec_flat(t) && spec_fields_flat(*rest),
    }
}

/// A struct whose end runs no destructor of the file: it has no destructor, and no field is a struct or a `std::unique_ptr`.
pub open spec fn spec_plain_struct(k: u32, sd: Structs) -> bool {
    spec_member(sd, k, DTOR_NAME) is None && match spec_get(sd, k) {
        Some((_, fields, _)) => spec_fields_flat(fields),
        None => false,
    }
}

pub open spec fn spec_plain_scalar(s: Scalar, sd: Structs) -> bool {
    match s {
        Scalar::Struct(k) => spec_plain_struct(k, sd),
        Scalar::Own(_) => false,
        _ => true,
    }
}

/// A type whose end runs no destructor of the file. A reference and a pointer own nothing.
pub open spec fn spec_plain_ty(t: Ty, sd: Structs) -> bool {
    match t {
        Ty::Seq(s, _) => spec_plain_scalar(s, sd),
        Ty::Vec(s) => spec_plain_scalar(s, sd),
        Ty::Opt(s) => spec_plain_scalar(s, sd),
        Ty::Variant(a, b) => spec_plain_scalar(a, sd) && spec_plain_scalar(b, sd),
        Ty::Struct(k) => spec_plain_struct(k, sd),
        Ty::Own(_) => false,
        Ty::Fresh(_) => false,
        Ty::Other(_) => false,
        _ => true,
    }
}

/// The type of the place that a write of the parameter of type `t` replaces: the value a reference names, or the value itself.
pub open spec fn spec_place_plain(t: Ty, sd: Structs) -> bool {
    match t {
        Ty::Mut(s) => spec_plain_scalar(s, sd),
        Ty::MutAfter(s) => spec_plain_scalar(s, sd),
        Ty::MutSeq(s) => spec_plain_scalar(s, sd),
        Ty::MutSeqAfter(s) => spec_plain_scalar(s, sd),
        _ => spec_plain_ty(t, sd),
    }
}

/// The value that a call gives. A constructor gives an object of its class.
pub open spec fn spec_ret_plain(t: Ty, sd: Structs) -> bool {
    match t {
        Ty::This(k) => spec_plain_struct(k, sd),
        Ty::ThisMut(k) => spec_plain_struct(k, sd),
        Ty::ThisAfter(k) => spec_plain_struct(k, sd),
        Ty::Fresh(k) => spec_plain_struct(k, sd),
        _ => spec_plain_ty(t, sd),
    }
}

/// The field `f` of the struct `k` has a plain type.
pub open spec fn spec_field_plain(k: u32, f: u32, sd: Structs) -> bool {
    match spec_get(sd, k) {
        Some((_, fields, _)) => match spec_get(fields, f) {
            Some(t) => spec_plain_ty(t, sd),
            None => false,
        },
        None => false,
    }
}

/// A write of the field `f` of the object of a member function with the parameters `ps` replaces a plain value.
pub open spec fn spec_this_field_plain(ps: Params, f: u32, sd: Structs) -> bool {
    match spec_head_ty(ps) {
        Some(Ty::This(k)) => spec_field_plain(k, f, sd),
        Some(Ty::ThisMut(k)) => spec_field_plain(k, f, sd),
        _ => false,
    }
}

pub open spec fn spec_params_end(ps: Params, sd: Structs) -> bool
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => !spec_plain_ty(t, sd) || spec_params_end(*rest, sd),
    }
}

/// A statement of a body with the parameters `ps` can end a life: a local that is not plain, or a write that can replace an
/// object. A statement with no rule here can end one.
pub open spec fn spec_stmt_ends(s: Stmt, ps: Params, sd: Structs) -> bool
    decreases s,
{
    match s {
        Stmt::Return(_, _) => false,
        Stmt::If(_, a, b, _) => spec_body_ends(*a, ps, sd) || spec_body_ends(*b, ps, sd),
        Stmt::Local(_, t, _, _) => !spec_plain_ty(t, sd),
        Stmt::Assign(v, _, _) => match spec_get(ps, v) {
            Some(t) => !spec_place_plain(t, sd),
            None => false,
        },
        Stmt::Step(_, _, _, _) => false,
        Stmt::While(_, _, b, _) => spec_body_ends(*b, ps, sd),
        Stmt::For(i, _, st, _, b, _) => spec_stmt_ends(*i, ps, sd) || spec_stmt_ends(*st, ps, sd) || spec_body_ends(*b, ps, sd),
        Stmt::SetField(f, _, _) => !spec_this_field_plain(ps, f, sd),
        Stmt::SetRefField(p, f, _, _) => match spec_get(ps, p) {
            Some(Ty::Mut(Scalar::Struct(k))) => !spec_field_plain(k, f, sd),
            _ => true,
        },
        Stmt::Switch(_, _, cs, _) => spec_cases_ends(*cs, ps, sd),
        Stmt::Call(_, _, _, _) => false,
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
        Stmt::RangeFor(_, _, t, _, _, b, _) => !spec_plain_ty(t, sd) || spec_body_ends(*b, ps, sd),
        Stmt::Block(b, _) => spec_body_ends(*b, ps, sd),
        _ => true,
    }
}

pub open spec fn spec_body_ends(ss: Stmts, ps: Params, sd: Structs) -> bool
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => spec_stmt_ends(*s, ps, sd) || spec_body_ends(*rest, ps, sd),
    }
}

pub open spec fn spec_cases_ends(cs: Cases, ps: Params, sd: Structs) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((_, b), rest) => spec_body_ends(*b, ps, sd) || spec_cases_ends(*rest, ps, sd),
    }
}

/// A call among `cs` gives a value that is not plain, which the caller ends unless it keeps it in a local.
pub open spec fn spec_rets_end(cs: List<(u32, bool, u32)>, all: Fns, sd: Structs) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _), rest) => (match spec_find(all, k) {
            Some(f) => !spec_ret_plain(f.ret, sd),
            None => false,
        }) || spec_rets_end(*rest, all, sd),
    }
}

/// A struct among `ks` that the body makes as a value is not plain.
pub open spec fn spec_made_end(ks: List<u32>, sd: Structs) -> bool
    decreases ks,
{
    match ks {
        List::Nil => false,
        List::Cons(k, rest) => !spec_plain_struct(k, sd) || spec_made_end(*rest, sd),
    }
}

/// The function `f` can end the life of an object whose end runs a destructor of the file, decision 0222. `ds` are the
/// destructors of the file.
pub open spec fn spec_may_end(f: Function, all: Fns, sd: Structs, ds: Names) -> bool {
    spec_has(ds, f.name)
        || spec_params_end(f.params, sd)
        || spec_body_ends(f.body, f.params, sd)
        || spec_rets_end(spec_ocalls_stmts(f.body), all, sd)
        || spec_made_end(spec_made_stmts(f.body), sd)
}

/// The keys of the functions of `fs` that can end such a life.
pub open spec fn spec_ends(fs: Fns, all: Fns, sd: Structs, ds: Names) -> Names
    decreases fs,
{
    match fs {
        List::Nil => List::Nil,
        List::Cons(f, rest) => if spec_may_end(*f, all, sd, ds) {
            List::Cons(f.name, Box::new(spec_ends(*rest, all, sd, ds)))
        } else {
            spec_ends(*rest, all, sd, ds)
        },
    }
}

pub fn flat_scalar(s: Scalar) -> (r: bool)
    ensures
        r == spec_flat_scalar(s),
{
    !matches!(s, Scalar::Struct(_)) && !matches!(s, Scalar::Own(_))
}

pub fn flat(t: Ty) -> (r: bool)
    ensures
        r == spec_flat(t),
{
    match t {
        Ty::I32 | Ty::I64 | Ty::U8 | Ty::U32 | Ty::U64 | Ty::I8 | Ty::I16 | Ty::U16 | Ty::F64 | Ty::Bool | Ty::Enum(_) => true,
        Ty::Seq(s, _) => flat_scalar(s),
        Ty::Vec(s) => flat_scalar(s),
        Ty::Opt(s) => flat_scalar(s),
        Ty::Variant(a, b) => flat_scalar(a) && flat_scalar(b),
        _ => false,
    }
}

pub fn fields_flat(ps: &Params) -> (r: bool)
    ensures
        r == spec_fields_flat(*ps),
    decreases ps,
{
    match ps {
        List::Nil => true,
        List::Cons((_, t), rest) => flat(*t) && fields_flat(rest),
    }
}

pub fn plain_struct(k: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_plain_struct(k, *sd),
{
    member(sd, k, DTOR_NAME).is_none() && match get_ref(sd, k) {
        Some((_, fields, _)) => fields_flat(fields),
        None => false,
    }
}

pub fn plain_scalar(s: Scalar, sd: &Structs) -> (r: bool)
    ensures
        r == spec_plain_scalar(s, *sd),
{
    match s {
        Scalar::Struct(k) => plain_struct(k, sd),
        Scalar::Own(_) => false,
        _ => true,
    }
}

pub fn plain_ty(t: Ty, sd: &Structs) -> (r: bool)
    ensures
        r == spec_plain_ty(t, *sd),
{
    match t {
        Ty::Seq(s, _) => plain_scalar(s, sd),
        Ty::Vec(s) => plain_scalar(s, sd),
        Ty::Opt(s) => plain_scalar(s, sd),
        Ty::Variant(a, b) => plain_scalar(a, sd) && plain_scalar(b, sd),
        Ty::Struct(k) => plain_struct(k, sd),
        Ty::Own(_) => false,
        Ty::Fresh(_) => false,
        Ty::Other(_) => false,
        _ => true,
    }
}

pub fn place_plain(t: Ty, sd: &Structs) -> (r: bool)
    ensures
        r == spec_place_plain(t, *sd),
{
    match t {
        Ty::Mut(s) => plain_scalar(s, sd),
        Ty::MutAfter(s) => plain_scalar(s, sd),
        Ty::MutSeq(s) => plain_scalar(s, sd),
        Ty::MutSeqAfter(s) => plain_scalar(s, sd),
        _ => plain_ty(t, sd),
    }
}

pub fn ret_plain(t: Ty, sd: &Structs) -> (r: bool)
    ensures
        r == spec_ret_plain(t, *sd),
{
    match t {
        Ty::This(k) => plain_struct(k, sd),
        Ty::ThisMut(k) => plain_struct(k, sd),
        Ty::ThisAfter(k) => plain_struct(k, sd),
        Ty::Fresh(k) => plain_struct(k, sd),
        _ => plain_ty(t, sd),
    }
}

pub fn field_plain(k: u32, f: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_field_plain(k, f, *sd),
{
    match get_ref(sd, k) {
        Some((_, fields, _)) => match get(fields, f) {
            Some(t) => plain_ty(t, sd),
            None => false,
        },
        None => false,
    }
}

pub fn this_field_plain(ps: &Params, f: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_this_field_plain(*ps, f, *sd),
{
    match head_ty(ps) {
        Some(Ty::This(k)) => field_plain(k, f, sd),
        Some(Ty::ThisMut(k)) => field_plain(k, f, sd),
        _ => false,
    }
}

pub fn params_end(ps: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_params_end(*ps, *sd),
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => !plain_ty(*t, sd) || params_end(rest, sd),
    }
}

pub fn stmt_ends(s: &Stmt, ps: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_stmt_ends(*s, *ps, *sd),
    decreases s,
{
    match s {
        Stmt::Return(_, _) => false,
        Stmt::If(_, a, b, _) => body_ends(a, ps, sd) || body_ends(b, ps, sd),
        Stmt::Local(_, t, _, _) => !plain_ty(*t, sd),
        Stmt::Assign(v, _, _) => match get(ps, *v) {
            Some(t) => !place_plain(t, sd),
            None => false,
        },
        Stmt::Step(_, _, _, _) => false,
        Stmt::While(_, _, b, _) => body_ends(b, ps, sd),
        Stmt::For(i, _, st, _, b, _) => stmt_ends(i, ps, sd) || stmt_ends(st, ps, sd) || body_ends(b, ps, sd),
        Stmt::SetField(f, _, _) => !this_field_plain(ps, *f, sd),
        Stmt::SetRefField(p, f, _, _) => match get(ps, *p) {
            Some(Ty::Mut(Scalar::Struct(k))) => !field_plain(k, *f, sd),
            _ => true,
        },
        Stmt::Switch(_, _, cs, _) => cases_ends(cs, ps, sd),
        Stmt::Call(_, _, _, _) => false,
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
        Stmt::RangeFor(_, _, t, _, _, b, _) => !plain_ty(*t, sd) || body_ends(b, ps, sd),
        Stmt::Block(b, _) => body_ends(b, ps, sd),
        _ => true,
    }
}

pub fn body_ends(ss: &Stmts, ps: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_body_ends(*ss, *ps, *sd),
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => stmt_ends(s, ps, sd) || body_ends(rest, ps, sd),
    }
}

pub fn cases_ends(cs: &Cases, ps: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_cases_ends(*cs, *ps, *sd),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((_, b), rest) => body_ends(b, ps, sd) || cases_ends(rest, ps, sd),
    }
}

pub fn rets_end(cs: &List<(u32, bool, u32)>, all: &Fns, sd: &Structs) -> (r: bool)
    ensures
        r == spec_rets_end(*cs, *all, *sd),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _), rest) => (match find(all, *k) {
            Some(f) => !ret_plain(f.ret, sd),
            None => false,
        }) || rets_end(rest, all, sd),
    }
}

pub fn made_end(ks: &List<u32>, sd: &Structs) -> (r: bool)
    ensures
        r == spec_made_end(*ks, *sd),
    decreases ks,
{
    match ks {
        List::Nil => false,
        List::Cons(k, rest) => !plain_struct(*k, sd) || made_end(rest, sd),
    }
}

pub fn may_end(f: &Function, all: &Fns, sd: &Structs, ds: &Names) -> (r: bool)
    ensures
        r == spec_may_end(*f, *all, *sd, *ds),
{
    has(ds, f.name)
        || params_end(&f.params, sd)
        || body_ends(&f.body, &f.params, sd)
        || rets_end(&ocalls_stmts(&f.body), all, sd)
        || made_end(&made_stmts(&f.body), sd)
}

pub fn ends(fs: &Fns, all: &Fns, sd: &Structs, ds: &Names) -> (r: Names)
    ensures
        r == spec_ends(*fs, *all, *sd, *ds),
    decreases fs,
{
    match fs {
        List::Nil => List::Nil,
        List::Cons(f, rest) => if may_end(f, all, sd, ds) {
            List::Cons(f.name, Box::new(ends(rest, all, sd, ds)))
        } else {
            ends(rest, all, sd, ds)
        },
    }
}

} // verus!

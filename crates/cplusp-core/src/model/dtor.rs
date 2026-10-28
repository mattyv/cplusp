//! The translator: a struct with a destructor, decision 0178. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ a struct with a destructor, decision 0178

/// The key of the destructor of the struct of a type: a value of a struct of the file whose table lists a destructor.
pub open spec fn spec_dtor_of(t: Ty, sd: Structs) -> Option<u32> {
    match t {
        Ty::Struct(k) => match spec_member(sd, k, DTOR_NAME) {
            Some((key, _)) => Some(key),
            None => None,
        },
        _ => None,
    }
}

pub fn dtor_of(t: Ty, sd: &Structs) -> (r: Option<u32>)
    ensures
        r == spec_dtor_of(t, *sd),
{
    match t {
        Ty::Struct(k) => match member(sd, k, DTOR_NAME) {
            Some((key, _)) => Some(key),
            None => None,
        },
        _ => None,
    }
}

/// A type that holds a struct with a destructor: the struct itself, a reference to it, or a sequence, an optional, a pointer or a
/// unique_ptr of it, decision 0178.
pub open spec fn spec_holds_dtor(t: Ty, sd: Structs) -> bool {
    match t {
        Ty::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        Ty::Seq(s, _) => spec_scalar_dtor(s, sd),
        Ty::Vec(s) => spec_scalar_dtor(s, sd),
        Ty::MutSeq(s) => spec_scalar_dtor(s, sd),
        Ty::MutSeqAfter(s) => spec_scalar_dtor(s, sd),
        Ty::Opt(s) => spec_scalar_dtor(s, sd),
        Ty::Own(s) => spec_scalar_dtor(s, sd),
        Ty::Ptr(s) => spec_scalar_dtor(s, sd),
        Ty::Mut(s) => spec_scalar_dtor(s, sd),
        Ty::MutAfter(s) => spec_scalar_dtor(s, sd),
        _ => false,
    }
}

pub open spec fn spec_scalar_dtor(s: Scalar, sd: Structs) -> bool {
    match s {
        Scalar::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        Scalar::Own(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        _ => false,
    }
}

pub fn scalar_dtor(s: Scalar, sd: &Structs) -> (r: bool)
    ensures
        r == spec_scalar_dtor(s, *sd),
{
    match s {
        Scalar::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        Scalar::Own(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        _ => false,
    }
}

pub fn holds_dtor(t: Ty, sd: &Structs) -> (r: bool)
    ensures
        r == spec_holds_dtor(t, *sd),
{
    match t {
        Ty::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        Ty::Seq(s, _) => scalar_dtor(s, sd),
        Ty::Vec(s) => scalar_dtor(s, sd),
        Ty::MutSeq(s) => scalar_dtor(s, sd),
        Ty::MutSeqAfter(s) => scalar_dtor(s, sd),
        Ty::Opt(s) => scalar_dtor(s, sd),
        Ty::Own(s) => scalar_dtor(s, sd),
        Ty::Ptr(s) => scalar_dtor(s, sd),
        Ty::Mut(s) => scalar_dtor(s, sd),
        Ty::MutAfter(s) => scalar_dtor(s, sd),
        _ => false,
    }
}

/// The locals of a scope whose type has a destructor, the newest first, which is the order in which they die.
pub open spec fn spec_live(env: Params, sd: Structs) -> Params
    decreases env,
{
    match env {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if spec_dtor_of(t, sd) is Some {
            List::Cons((n, t), Box::new(spec_live(*rest, sd)))
        } else {
            spec_live(*rest, sd)
        },
    }
}

pub fn live(env: &Params, sd: &Structs) -> (r: Params)
    ensures
        r == spec_live(*env, *sd),
    decreases env,
{
    match env {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if dtor_of(*t, sd).is_some() {
            List::Cons((*n, *t), Box::new(live(rest, sd)))
        } else {
            live(rest, sd)
        },
    }
}

/// The locals that the statements of a block declare at its top, the newest first, after the locals `acc`.
pub open spec fn spec_block_locals(ss: Stmts, acc: Params) -> Params
    decreases ss,
{
    match ss {
        List::Nil => acc,
        List::Cons(s, rest) => spec_block_locals(*rest, spec_scope(*s, acc)),
    }
}

pub fn block_locals(ss: &Stmts, acc: Params) -> (r: Params)
    ensures
        r == spec_block_locals(*ss, acc),
    decreases ss,
{
    match ss {
        List::Nil => acc,
        List::Cons(s, rest) => block_locals(rest, scope(s, &acc)),
    }
}

/// The last statement of a block is a return or an exit, so nothing runs at the end of the block.
pub open spec fn spec_ends_out(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => if *rest is Nil {
            *s is Return || *s is Exit
        } else {
            spec_ends_out(*rest)
        },
    }
}

pub fn ends_out(ss: &Stmts) -> (r: bool)
    ensures
        r == spec_ends_out(*ss),
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => if matches!(**rest, List::Nil) {
            matches!(**s, Stmt::Return(..) | Stmt::Exit(..))
        } else {
            ends_out(rest)
        },
    }
}

/// The place of the last statement of a block.
pub open spec fn spec_last_place(ss: Stmts) -> u32
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons(s, rest) => if *rest is Nil {
            spec_place(*s)
        } else {
            spec_last_place(*rest)
        },
    }
}

pub fn last_place(ss: &Stmts) -> (r: u32)
    ensures
        r == spec_last_place(*ss),
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons(s, rest) => if matches!(**rest, List::Nil) {
            place(s)
        } else {
            last_place(rest)
        },
    }
}

/// The arguments for the globals of a destructor: each is the parameter of the caller with the name of the global. A caller
/// that does not list the global gives the name, which the translation refuses.
pub open spec fn spec_dtor_globals(dps: Params, ps: Params) -> Args
    decreases dps,
{
    match dps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(
            Box::new(match spec_get(ps, g) {
                Some(t) => Expr::Var(g, t),
                None => Expr::Name(g),
            }),
            Box::new(spec_dtor_globals(*rest, ps)),
        ),
    }
}

pub fn dtor_globals(dps: &Params, ps: &Params) -> (r: Args)
    ensures
        r == spec_dtor_globals(*dps, *ps),
    decreases dps,
{
    match dps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(
            Box::new(match get(ps, *g) {
                Some(t) => Expr::Var(*g, t),
                None => Expr::Name(*g),
            }),
            Box::new(dtor_globals(rest, ps)),
        ),
    }
}

/// The call of the destructor of the local `v` of type `t`, as a call that stands alone: the local as its object, then its
/// globals.
pub open spec fn spec_dtor_call(v: u32, t: Ty, all: Fns, ps: Params, sd: Structs, line: u32) -> Result<DStmt, Refusal> {
    match spec_dtor_of(t, sd) {
        None => Err(Refusal::Syntax(line)),
        Some(key) => match spec_find(all, key) {
            None => Err(Refusal::Syntax(line)),
            Some(f) => spec_call_stmt(key, DTOR_NAME, List::Cons(Box::new(Expr::Var(v, t)), Box::new(spec_dtor_globals(spec_tail(f.params), ps))), line, all, ps, sd),
        },
    }
}

pub fn dtor_call(v: u32, t: Ty, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dtor_call(v, t, *all, *ps, *sd, line),
{
    match dtor_of(t, sd) {
        None => Err(Refusal::Syntax(line)),
        Some(key) => match find(all, key) {
            None => Err(Refusal::Syntax(line)),
            Some(f) => {
                let args = List::Cons(Box::new(Expr::Var(v, t)), Box::new(dtor_globals(&tail(&f.params), ps)));
                call_stmt(key, DTOR_NAME, &args, line, all, ps, sd)
            },
        },
    }
}

/// The calls of the destructors of the locals `ls`, in their order.
pub open spec fn spec_dtor_calls(ls: Params, all: Fns, ps: Params, sd: Structs, line: u32) -> Result<DStmts, Refusal>
    decreases ls,
{
    match ls {
        List::Nil => Ok(List::Nil),
        List::Cons((v, t), rest) => match spec_dtor_call(v, t, all, ps, sd, line) {
            Err(r) => Err(r),
            Ok(d) => match spec_dtor_calls(*rest, all, ps, sd, line) {
                Err(r) => Err(r),
                Ok(ds) => Ok(List::Cons((Box::new(d), line), Box::new(ds))),
            },
        },
    }
}

pub fn dtor_calls(ls: &Params, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_dtor_calls(*ls, *all, *ps, *sd, line),
    decreases ls,
{
    match ls {
        List::Nil => Ok(List::Nil),
        List::Cons((v, t), rest) => match dtor_call(*v, *t, all, ps, sd, line) {
            Err(r) => Err(r),
            Ok(d) => match dtor_calls(rest, all, ps, sd, line) {
                Err(r) => Err(r),
                Ok(ds) => Ok(List::Cons((Box::new(d), line), Box::new(ds))),
            },
        },
    }
}

/// The destructors that run at the end of a block, for the locals it declares, unless the block ends with a return or an exit.
pub open spec fn spec_block_end(ss: Stmts, all: Fns, ps: Params, sd: Structs) -> Result<Option<DStmt>, Refusal> {
    let ls = spec_live(spec_block_locals(ss, List::Nil), sd);
    if ls is Nil || spec_ends_out(ss) {
        Ok(None)
    } else {
        match spec_dtor_calls(ls, all, ps, sd, spec_last_place(ss)) {
            Err(r) => Err(r),
            Ok(ds) => Ok(Some(DStmt::Dtors(Box::new(ds)))),
        }
    }
}

pub fn block_end(ss: &Stmts, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<Option<DStmt>, Refusal>)
    ensures
        r == spec_block_end(*ss, *all, *ps, *sd),
{
    let ls = live(&block_locals(ss, List::Nil), sd);
    if matches!(ls, List::Nil) || ends_out(ss) {
        Ok(None)
    } else {
        match dtor_calls(&ls, all, ps, sd, last_place(ss)) {
            Err(r) => Err(r),
            Ok(ds) => Ok(Some(DStmt::Dtors(Box::new(ds)))),
        }
    }
}

/// An expression that copies a value of a struct with a destructor: a name of such a type, or a reference parameter of one.
pub open spec fn spec_dtor_copy(e: Expr, sd: Structs) -> bool
    decreases e,
{
    match e {
        Expr::Var(_, t) => spec_dtor_of(t, sd) is Some || match t {
            Ty::Mut(Scalar::Struct(k)) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            _ => false,
        },
        Expr::Cast(c, a) => (c == CastKind::Read || c == CastKind::NoOp) && spec_dtor_copy(*a, sd),
        Expr::Paren(a) => spec_dtor_copy(*a, sd),
        _ => false,
    }
}

pub fn dtor_copy(e: &Expr, sd: &Structs) -> (r: bool)
    ensures
        r == spec_dtor_copy(*e, *sd),
    decreases e,
{
    match e {
        Expr::Var(_, t) => dtor_of(*t, sd).is_some() || match t {
            Ty::Mut(Scalar::Struct(k)) => dtor_of(Ty::Struct(*k), sd).is_some(),
            _ => false,
        },
        Expr::Cast(c, a) => (*c == CastKind::Read || *c == CastKind::NoOp) && dtor_copy(a, sd),
        Expr::Paren(a) => dtor_copy(a, sd),
        _ => false,
    }
}

/// The callee gives a value of a struct with a destructor: a constructor of one, or a function that gives one.
pub open spec fn spec_callee_dtor(all: Fns, key: u32, sd: Structs) -> bool {
    match spec_find(all, key) {
        Some(f) => match f.ret {
            Ty::This(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            Ty::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            _ => false,
        },
        None => false,
    }
}

pub fn callee_dtor(all: &Fns, key: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_callee_dtor(*all, key, *sd),
{
    match find(all, key) {
        Some(f) => match f.ret {
            Ty::This(k) => dtor_of(Ty::Struct(k), sd).is_some(),
            Ty::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
            _ => false,
        },
        None => false,
    }
}

/// The check of a local of a struct with a destructor: its start value is a call of a constructor of the struct, and the
/// destructor has a contract.
pub open spec fn spec_dtor_local(t: Ty, e: Expr, all: Fns, sd: Structs, line: u32) -> Option<Refusal> {
    match t {
        Ty::Struct(k) => match spec_dtor_of(t, sd) {
            None => None,
            Some(key) => if !(match e {
                Expr::Call(c, _, _, _) => match spec_find(all, c) {
                    Some(f) => f.ret == Ty::This(k),
                    None => false,
                },
                _ => false,
            }) {
                Some(Refusal::Copy(line))
            } else if match spec_find(all, key) {
                Some(f) => f.conds is Nil,
                None => true,
            } {
                Some(Refusal::NoDtorContract(line))
            } else {
                None
            },
        },
        _ => if spec_holds_dtor(t, sd) { Some(Refusal::Copy(line)) } else { None },
    }
}

pub fn dtor_local(t: Ty, e: &Expr, all: &Fns, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_dtor_local(t, *e, *all, *sd, line),
{
    match t {
        Ty::Struct(k) => match dtor_of(t, sd) {
            None => None,
            Some(key) => {
                let made = match e {
                    Expr::Call(c, _, _, _) => match find(all, *c) {
                        Some(f) => f.ret == Ty::This(k),
                        None => false,
                    },
                    _ => false,
                };
                if !made {
                    Some(Refusal::Copy(line))
                } else if match find(all, key) {
                    Some(f) => matches!(f.conds, List::Nil),
                    None => true,
                } {
                    Some(Refusal::NoDtorContract(line))
                } else {
                    None
                }
            },
        },
        _ => if holds_dtor(t, sd) { Some(Refusal::Copy(line)) } else { None },
    }
}

/// A return of a function with locals that have destructors: the value, then each destructor, newest first, then the exit.
pub open spec fn spec_dying_return(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    // A value that runs a call only sometimes sets the result in each branch, decision 0177.
    if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        match spec_lower(e, None, true, all, l, sd, 0) {
            Err(r) => Err(r),
            Ok((ss, _)) => match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
                Err(r) => Err(r),
                Ok(ds) => Ok(DStmt::Block(Box::new(spec_append(
                    ss,
                    List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))),
                )))),
            },
        }
    } else {
    match spec_lift(e, all, l, sd, 0, true) {
        Err(r) => Err(r),
        Ok((c, d, _)) => match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
            Err(r) => Err(r),
            Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons(
                (Box::new(spec_pre(c, DStmt::SetResult(d))), l),
                Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))),
            )))),
        },
    }
    }
}

pub fn dying_return(e: &Expr, l: u32, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dying_return(*e, l, *all, *env, *ps, *sd),
{
    if !matches!(e, Expr::Call(..)) && cond_calls(e, all, l, sd) {
        match lower(e, None, true, all, l, sd, 0) {
            Err(r) => Err(r),
            Ok((ss, _)) => match dtor_calls(&live(env, sd), all, ps, sd, l) {
                Err(r) => Err(r),
                Ok(ds) => Ok(DStmt::Block(Box::new(append(
                    ss,
                    List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))),
                )))),
            },
        }
    } else {
    match lift(e, all, l, sd, 0, true) {
        Err(r) => Err(r),
        Ok((c, d, _)) => match dtor_calls(&live(env, sd), all, ps, sd, l) {
            Err(r) => Err(r),
            Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons(
                (Box::new(pre(c, DStmt::SetResult(d))), l),
                Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))),
            )))),
        },
    }
    }
}

/// An exit of a function with locals that have destructors runs each destructor first.
pub open spec fn spec_dying_exit(l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
        Err(r) => Err(r),
        Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))))),
    }
}

pub fn dying_exit(l: u32, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dying_exit(l, *all, *env, *ps, *sd),
{
    match dtor_calls(&live(env, sd), all, ps, sd, l) {
        Err(r) => Err(r),
        Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))))),
    }
}

/// A call that stands alone names a key with a method.
pub proof fn lemma_call_stmt_resolves(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_call_stmt(key, name, args, line, all, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_call_stmt(key, name, args, line, all, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 3);
    if spec_call_lift(key, name, args, line, all, line, sd).is_ok() {
        lemma_call_lift_resolves(key, name, args, line, all, line, sd);
    }
    if let List::Cons(_, rest) = args {
        if spec_call_lift(key, name, *rest, line, all, line, sd).is_ok() {
            lemma_call_lift_resolves(key, name, *rest, line, all, line, sd);
        }
    }
}

/// The calls of destructors name keys with methods.
pub proof fn lemma_dtor_calls_resolve(ls: Params, all: Fns, ps: Params, sd: Structs, line: u32)
    requires
        spec_dtor_calls(ls, all, ps, sd, line).is_ok(),
    ensures
        calls_resolve(spec_dtor_calls(ls, all, ps, sd, line).unwrap(), all, sd),
    decreases ls,
{
    match ls {
        List::Nil => {},
        List::Cons((v, t), rest) => {
            let key = spec_dtor_of(t, sd).unwrap();
            let f = spec_find(all, key).unwrap();
            lemma_call_stmt_resolves(key, DTOR_NAME, List::Cons(Box::new(Expr::Var(v, t)), Box::new(spec_dtor_globals(spec_tail(f.params), ps))), line, all, ps, sd);
            lemma_dtor_calls_resolve(*rest, all, ps, sd, line);
        },
    }
}

pub proof fn lemma_block_end_resolves(ss: Stmts, all: Fns, ps: Params, sd: Structs)
    requires
        spec_block_end(ss, all, ps, sd).is_ok(),
    ensures
        match spec_block_end(ss, all, ps, sd).unwrap() {
            Some(d) => calls_resolve(List::Cons((Box::new(d), spec_last_place(ss)), Box::new(List::Nil)), all, sd),
            None => true,
        },
{
    reveal_with_fuel(calls_resolve, 2);
    let ls = spec_live(spec_block_locals(ss, List::Nil), sd);
    if !(ls is Nil || spec_ends_out(ss)) {
        lemma_dtor_calls_resolve(ls, all, ps, sd, spec_last_place(ss));
    }
}

/// The start value of a local that is no vector: a call, or an expression whose calls run first, decision 0104.
pub open spec fn spec_local_value(n: u32, dt: DTy, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match e {
        Expr::Call(k, nm, args, at) => spec_local_call(n, dt, k, nm, *args, at, all, l, ps, sd),
        _ => match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, d))),
            Err(r) => Err(r),
        },
    }
}

pub fn local_value(n: u32, dt: DTy, e: &Expr, l: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_local_value(n, dt, *e, l, *all, *ps, *sd),
{
    match e {
        Expr::Call(k, nm, args, at) => local_call(n, dt, *k, *nm, args, *at, all, l, ps, sd),
        _ => match lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(pre(c, DStmt::Local(n, dt, d))),
            Err(r) => Err(r),
        },
    }
}

/// A `return`. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_return_stmt(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    // A return can move a local or a parameter, decision 0171. Nothing runs after it, so it sets nothing to null.
    match spec_move_check(spec_unmove(e).1, spec_var_names(e), ps, true, l) {
        Some(r) => Err(r),
        // A copy of a struct with a destructor has no rule, and the locals with destructors die after the value, decision 0178.
        None => if spec_dtor_copy(spec_unmove(e).0, sd) {
            Err(Refusal::Copy(l))
        } else if spec_live(env, sd) is Nil {
            spec_return(spec_unmove(e).0, l, all, ps, sd)
        } else {
            spec_dying_return(spec_unmove(e).0, l, all, env, ps, sd)
        },
    }
}

/// A local. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_local_stmt(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match t {
        // A local vector is a copy of a sequence in scope of the same element, decision 0160, or the vector that a call gives,
        // decision 0163. A vector of a struct with a destructor is a copy, decision 0178.
        Ty::Vec(s) => if spec_holds_dtor(Ty::Vec(s), sd) { Err(Refusal::Copy(l)) } else { match spec_value_ty(Ty::Vec(s), l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => spec_local_call(n, dt, k, nm, *args, at, all, l, ps, sd),
                // The source is a name in scope, decision 0164.
                Expr::Copy(a, from, _) => if spec_seq_elem(from) == Some(s) && match *a {
                    Expr::Var(w, _) => spec_get(env, w) is Some || spec_get(ps, w) is Some,
                    _ => false,
                } {
                    match spec_lift(e, all, l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, d))),
                        Err(r) => Err(r),
                    }
                } else {
                    Err(Refusal::VecLocal(l))
                },
                // A local vector with no initial value is the empty sequence, decision 0170.
                Expr::EmptyVec => Ok(DStmt::Local(n, dt, DExpr::EmptySeq)),
                // `v(n, x)` is a vector of n copies of x, decision 0185. The count lifts first, then the value.
                Expr::Fill(c, x) => match spec_lift(*c, all, l, sd, 0, true) {
                    Err(r) => Err(r),
                    Ok((c1, dc, n1)) => match spec_lift(*x, all, l, sd, n1, true) {
                        Err(r) => Err(r),
                        Ok((c2, dx, _)) => Ok(spec_pre(spec_append(c1, c2), DStmt::Local(n, dt, DExpr::SeqFill(Box::new(dc), Box::new(dx))))),
                    },
                },
                // A move of a vector gives the local its value, and the source then has any value, decision 0185.
                Expr::Move(w, _) => match spec_get(ps, w) {
                    Some(Ty::MutSeq(s2)) => if s2 == s {
                        Ok(DStmt::Gone(Box::new(DStmt::Local(n, dt, DExpr::Out(w))), w, true))
                    } else {
                        Err(Refusal::VecLocal(l))
                    },
                    Some(_) => Err(Refusal::WriteParam(w, l)),
                    None => match spec_get(env, w) {
                        Some(Ty::Vec(s2)) => if s2 == s {
                            Ok(DStmt::Gone(Box::new(DStmt::Local(n, dt, DExpr::Var(w))), w, false))
                        } else {
                            Err(Refusal::VecLocal(l))
                        },
                        _ => Err(Refusal::VecLocal(l)),
                    },
                },
                _ => Err(Refusal::VecLocal(l)),
            },
        } },
        // A local std::array from a brace list of its length is the sequence of the values, decision 0184.
        Ty::Seq(_, Extent::Fixed(k)) => if spec_holds_dtor(t, sd) { Err(Refusal::Copy(l)) } else { match e {
            Expr::List(args) => if spec_count_args(*args) as u64 != k {
                Err(Refusal::BraceLen(spec_count_args(*args), spec_extent32(k), l))
            } else {
                match spec_ty(t, l) {
                    Err(r) => Err(r),
                    Ok(dt) => match spec_lift_args(*args, all, l, sd, 0, true) {
                        Ok((c, da, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, DExpr::SeqLit(Box::new(da))))),
                        Err(r) => Err(r),
                    },
                }
            },
            // `k` copies of a value start an array of length `k`, as the value-initialized field of 0196.
            Expr::Fill(c, x) => match *c {
                Expr::Lit(m, _) => if m == k {
                    match spec_ty(t, l) {
                        Err(r) => Err(r),
                        Ok(dt) => match spec_lift(*x, all, l, sd, 0, true) {
                            Ok((cx, dx, _)) => Ok(spec_pre(cx, DStmt::Local(n, dt, DExpr::SeqFill(Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(m)))), Box::new(dx))))),
                            Err(r) => Err(r),
                        },
                    }
                } else {
                    Err(Refusal::SeqParam(l))
                },
                _ => Err(Refusal::SeqParam(l)),
            },
            _ => Err(Refusal::SeqParam(l)),
        } },
        // The start value of a local can move a local, decision 0171.
        _ => match spec_value_ty(t, l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match spec_dtor_local(t, e, all, sd, l) {
                Some(r) => Err(r),
                None => match spec_move_check(spec_unmove(e).1, spec_var_names(e), ps, false, l) {
                    Some(r) => Err(r),
                    None => match spec_local_value(n, dt, spec_unmove(e).0, l, all, ps, sd) {
                        Ok(d) => Ok(spec_moved(d, spec_unmove(e).1, spec_vec_moves(e))),
                        Err(r) => Err(r),
                    },
                },
            },
        },
    }
}

/// An assignment. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_assign_stmt(n: u32, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    if spec_is_mut(ps, n) {
        match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetOut(n, d))),
            Err(r) => Err(r),
        }
    } else if (spec_get(ps, n) is Some) {
        Err(Refusal::WriteParam(n, l))
    } else {
        match e {
            // The value of a call that gives a struct with a destructor is a temporary, decision 0178.
            Expr::Call(k, nm, args, at) => if spec_callee_dtor(all, k, sd) {
                Err(Refusal::Copy(l))
            } else if spec_callee_writes(all, k) {
                Err(Refusal::Place(at))
            } else {
                match spec_call_lift(k, nm, *args, at, all, l, sd) {
                    Ok((c, da)) => Ok(spec_pre(c, DStmt::AssignCall(n, k, da))),
                    Err(r) => Err(r),
                }
            },
            _ => match spec_lift(e, all, l, sd, 0, true) {
                Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Assign(n, d))),
                Err(r) => Err(r),
            },
        }
    }
}

/// A statement of the body, and a list of them. `env` is the variables in scope, and `ps` the parameters. A call runs before its
/// statement where C++ runs it once, decision 0104, and a call of a function that writes its object or gives no value stands
/// alone. A write is to a local, never to a parameter, or to a field of the object of a member function that writes it, decision
/// 0096.
// ponytail: `x = o.f();` of a function that writes its object is refused as a call out of place. Upgrade: an update to a fresh
// local, then the write. `return o.f();` writes back and returns, decision 0174.
pub open spec fn spec_stmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal>
    decreases s, 0nat,
{
    match s {
        Stmt::Return(e, l) => spec_return_stmt(e, l, all, env, ps, sd),
        Stmt::If(c, t, f, l) => match spec_lift(c, all, l, sd, 0, true) {
            Ok((cc, dc, _)) => match spec_stmts(*t, all, env, ps, sd) {
                Ok(dt) => match spec_stmts(*f, all, env, ps, sd) {
                    Ok(df) => Ok(spec_pre(cc, DStmt::If(dc, Box::new(dt), Box::new(df)))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => spec_local_stmt(n, t, e, l, all, env, ps, sd),
        Stmt::Assign(n, e, l) => spec_assign_stmt(n, e, l, all, ps, sd),
        // `++` and `--` on a double round, decision 0150.
        Stmt::Step(n, t, up, l) => if t == Ty::F64 {
            Err(Refusal::Rounds(l))
        } else if (spec_get(ps, n) is Some) && !spec_is_mut(ps, n) {
            Err(Refusal::WriteParam(n, l))
        } else {
            match spec_ty(t, l) {
                Err(r) => Err(r),
                Ok(dt) => Ok(spec_step(n, dt, up, spec_is_mut(ps, n))),
            }
        },
        Stmt::While(c, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, env, sd, false) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, env, sd, false) {
                Err(r) => Err(r),
                Ok(dec) => match spec_loop_test(c, all, l, sd) {
                    Err(r) => Err(r),
                    Ok(dc) => match spec_stmts(*body, all, env, ps, sd) {
                        Err(r) => Err(r),
                        Ok(db) => Ok(DStmt::While(dc, inv, dec, Box::new(db))),
                    },
                },
            },
        },
        Stmt::For(init, c, step, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, spec_scope(*init, env), sd, false) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, spec_scope(*init, env), sd, false) {
                Err(r) => Err(r),
                Ok(dec) => match spec_stmt(*init, all, env, ps, sd) {
                    Err(r) => Err(r),
                    Ok(di) => match spec_loop_test(c, all, l, sd) {
                        Err(r) => Err(r),
                        Ok(dc) => match spec_stmt(*step, all, spec_scope(*init, env), ps, sd) {
                            Err(r) => Err(r),
                            Ok(ds) => match spec_stmts(*body, all, spec_scope(*init, env), ps, sd) {
                                Err(r) => Err(r),
                                Ok(db) => Ok(DStmt::For(Box::new(di), spec_place(*init), dc, inv, dec, Box::new(db), Box::new(ds), spec_place(*step))),
                            },
                        },
                    },
                },
            },
        },
        // A range-for is a for loop over the indexes of its sequence parameter, decision 0143. The index is new, the core adds the
        // invariant `i <= v.size()` first, so that the invariants of the author can slice `v[..i]`, and, when the author wrote none,
        // the decreases line `v.size() - i`. Each turn starts with `x = v[i]`.
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match spec_index_of(*lc, fresh) {
            Err(r) => Err(r),
            // An index is new: no variable in scope, and no field of the object, decision 0144.
            Ok((i, il)) => if spec_has(spec_keys(env), i) || spec_this_field(ps, None, i, sd) is Some {
                Err(Refusal::IndexName(i, il))
            } else {
                match seq {
                    Expr::Var(v, Ty::Seq(s, ext)) => if xt != spec_elem(s) {
                        Err(Refusal::Syntax(l))
                    } else {
                        let inner = List::Cons((i, Ty::U64), Box::new(env));
                        match spec_loop_conds(*lc, CondKind::Invariant, inner, sd, true) {
                            Err(r) => Err(r),
                            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, inner, sd, true) {
                                Err(r) => Err(r),
                                Ok(dec) => match spec_contract(spec_range_bound(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd) {
                                    Err(r) => Err(r),
                                    Ok(dbound) => match spec_contract(spec_range_measure(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd) {
                                        Err(r) => Err(r),
                                        Ok(dmeasure) => match spec_code(spec_range_test(i, v, s, ext), l) {
                                            Err(r) => Err(r),
                                            Ok(dc) => match spec_value_ty(xt, l, sd) {
                                                Err(r) => Err(r),
                                                Ok(dt) => match spec_code(spec_range_elem(i, v, s, ext), l) {
                                                    Err(r) => Err(r),
                                                    Ok(de) => match spec_stmts(*body, all, List::Cons((x, xt), Box::new(inner)), ps, sd) {
                                                        Err(r) => Err(r),
                                                        Ok(db) => Ok(DStmt::For(
                                                            Box::new(DStmt::Local(i, DTy::UInt64, spec_range_zero())),
                                                            l,
                                                            dc,
                                                            List::Cons((dbound, l), Box::new(inv)),
                                                            if dec is Nil {
                                                                List::Cons((dmeasure, l), Box::new(List::Nil))
                                                            } else {
                                                                dec
                                                            },
                                                            Box::new(List::Cons((Box::new(DStmt::Local(x, dt, de)), l), Box::new(db))),
                                                            Box::new(spec_step(i, DTy::UInt64, true, false)),
                                                            l,
                                                        )),
                                                    },
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        }
                    },
                    _ => Err(Refusal::Syntax(l)),
                }
            },
        },
        Stmt::SetField(f, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                    Some(_) => match spec_lift(e, all, l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetField(f, d))),
                        Err(r) => Err(r),
                    },
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::SetRefField(p, f, e, l) => match spec_get(ps, p) {
            Some(Ty::Mut(Scalar::Struct(k))) => match spec_field_ty(sd, k, f) {
                Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                Some(_) => match spec_lift(e, all, l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetOutField(p, f, d))),
                    Err(r) => Err(r),
                },
                None => Err(Refusal::NoField(f, l)),
            },
            Some(_) => Err(Refusal::WriteParam(p, l)),
            None => Err(Refusal::Syntax(l)),
        },
        // A write through a local unique_ptr writes the value that it owns. The value can move a local, and the statement reads
        // the pointer, so the pointer cannot move in it, decision 0186.
        Stmt::SetOwnField(n, f, e, l) => if spec_get(ps, n) is Some {
            Err(Refusal::WriteParam(n, l))
        } else {
            match spec_get(env, n) {
                Some(Ty::Own(Scalar::Struct(k))) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                    Some(_) => match spec_move_check(spec_unmove(e).1, List::Cons(n, Box::new(spec_var_names(e))), ps, false, l) {
                        Some(r) => Err(r),
                        None => match spec_lift(spec_unmove(e).0, all, l, sd, 0, true) {
                            Ok((c, d, _)) => Ok(spec_moved(spec_pre(c, DStmt::SetOwnField(n, f, d)), spec_unmove(e).1, spec_vec_moves(e))),
                            Err(r) => Err(r),
                        },
                    },
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::Syntax(l)),
            }
        },
        Stmt::Switch(e, k, cs, l) => match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => match spec_cases(*cs, all, env, ps, sd) {
                Ok(dc) => Ok(spec_pre(c, DStmt::Match(d, k, Box::new(dc)))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        // A call that stands alone can move a local, decision 0171.
        Stmt::Call(k, nm, args, l) => match spec_move_check(spec_unmove_args(*args).1, spec_var_names_args(*args), ps, false, l) {
            Some(r) => Err(r),
            None => match spec_call_stmt(k, nm, spec_unmove_args(*args).0, l, all, ps, sd) {
                Ok(d) => Ok(spec_moved(d, spec_unmove_args(*args).1, spec_vec_moves_args(*args))),
                Err(r) => Err(r),
            },
        },
        Stmt::Exit(l) => if spec_live(env, sd) is Nil {
            Ok(DStmt::Exit)
        } else {
            spec_dying_exit(l, all, env, ps, sd)
        },
        Stmt::Block(b, _) => match spec_stmts(*b, all, env, ps, sd) {
            Ok(db) => Ok(DStmt::Scope(Box::new(db))),
            Err(r) => Err(r),
        },
        Stmt::Assert(e, l) => match spec_contract(e, spec_keys(env), spec_after(env), None, List::Nil, l, sd) {
            Ok(d) => Ok(DStmt::Assert(d)),
            Err(r) => Err(r),
        },
        Stmt::Apply(f, args, l) => match spec_contract_args(*args, spec_keys(env), spec_after(env), None, List::Nil, l, sd) {
            Ok(da) => Ok(DStmt::Apply(f, da)),
            Err(r) => Err(r),
        },
        // `v[i] = e` writes one element of a vector by reference, decision 0145. The index and the value hold no call.
        // ponytail: a call in the index or the value is refused as out of place, so the author sets a local first. Upgrade: lift the
        // calls as `Stmt::Assign` does, decision 0104.
        Stmt::SetIndex(v, i, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(_)) => match spec_code(i, l) {
                Ok(di) => match spec_code(e, l) {
                    Ok(de) => Ok(DStmt::SetOut(v, DExpr::SetAt(Box::new(DExpr::Out(v)), Box::new(di), Box::new(de)))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            // A write to a local vector is a new value of the local, decision 0160, and so is a write to a local std::array,
            // decision 0184.
            None => match spec_get(env, v) {
                Some(Ty::Vec(_)) => match spec_code(i, l) {
                    Ok(di) => match spec_code(e, l) {
                        Ok(de) => Ok(DStmt::Assign(v, DExpr::SetAt(Box::new(DExpr::Var(v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                Some(Ty::Seq(_, Extent::Fixed(_))) => match spec_code(i, l) {
                    Ok(di) => match spec_code(e, l) {
                        Ok(de) => Ok(DStmt::Assign(v, DExpr::SetAt(Box::new(DExpr::Var(v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(l)),
            },
        },
        // `f[i] = e` of a sequence field in a member function that writes its object is a new value of the field, decision 0187.
        Stmt::SetFieldAt(f, i, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => match spec_code(i, l) {
                        Ok(di) => match spec_code(e, l) {
                            Ok(de) => Ok(DStmt::SetField(f, DExpr::SetAt(Box::new(DExpr::Field(Box::new(DExpr::After), f)), Box::new(di), Box::new(de)))),
                            Err(r) => Err(r),
                        },
                        Err(r) => Err(r),
                    },
                    Some(_) => Err(Refusal::Syntax(l)),
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        // `f.push_back(e)` and `f.pop_back()` of a sequence field in a member function that writes its object are new values of the
        // field, decision 0191. A pop is PopBack of the prelude, whose requires line Dafny checks.
        // ponytail: the value of a push is code with no call. Upgrade: run its calls before it, as PushBack does, decision 0170.
        // `f->g = e` writes the field `g` of the struct that the unique_ptr field `f` of the object owns, decision 0197. Dafny proves
        // that `f` holds a value.
        // ponytail: the value is code with no call. Upgrade: run its calls before it, as for SetOwnField, decision 0186.
        Stmt::SetThroughField(f, g, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Own(Scalar::Struct(k2))) => match spec_field_ty(sd, k2, g) {
                        Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                        Some(_) => match spec_code(e, l) {
                            Ok(de) => Ok(DStmt::SetThroughField(f, g, de)),
                            Err(r) => Err(r),
                        },
                        None => Err(Refusal::NoField(g, l)),
                    },
                    Some(_) => Err(Refusal::Syntax(l)),
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::PushField(f, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => match spec_code(e, l) {
                        Ok(de) => Ok(DStmt::SetField(f, DExpr::Append(Box::new(DExpr::Field(Box::new(DExpr::After), f)), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Some(_) => Err(Refusal::Syntax(l)),
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::PopField(f, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Ok(DStmt::SetField(f, DExpr::PopBack(Box::new(DExpr::Field(Box::new(DExpr::After), f))))),
                    Some(_) => Err(Refusal::Syntax(l)),
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        // `v.push_back(e)` appends one element, decision 0148. A failed push_back throws and never returns to verified code.
        // ponytail: a call in the value is refused as out of place, as for SetIndex. Upgrade: lift the calls, decision 0104.
        // `v.push_back(std::make_unique<D>(a))` runs the constructor of `D` before it, decision 0170.
        Stmt::PushBack(v, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(_)) => match spec_push_value(e, all, l, sd) {
                Ok((c, de)) => Ok(spec_pre(c, DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(de))))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(_)) => match spec_push_value(e, all, l, sd) {
                    Ok((c, de)) => Ok(spec_pre(c, DStmt::Assign(v, DExpr::Append(Box::new(DExpr::Var(v)), Box::new(de))))),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(l)),
            },
        },
        // `std::sort(v.begin(), v.end())` of a vector of integers, decision 0161.
        Stmt::Sort(v, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(s)) => spec_sort(DExpr::Out(v), s, l),
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(s)) => spec_sort(DExpr::Var(v), s, l),
                _ => Err(Refusal::SortForm(l)),
            },
        },
        // `std::sort` with a comparator lambda, decision 0162.
        Stmt::SortBy(v, a, b, t, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(s)) => spec_sort_by(DExpr::Out(v), s, a, b, t, e, l),
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(s)) => spec_sort_by(DExpr::Var(v), s, a, b, t, e, l),
                _ => Err(Refusal::SortForm(l)),
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// The cases of a switch, each body over the variables in scope at the switch, decision 0109.
pub open spec fn spec_cases(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DCases, Refusal>
    decreases cs, 0nat,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((i, body), rest) => match spec_stmts(*body, all, env, ps, sd) {
            Ok(db) => match spec_cases(*rest, all, env, ps, sd) {
                Ok(dr) => Ok(List::Cons((i, Box::new(db)), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The statements of a block, then the destructors of the locals that the block declares, decision 0178.
pub open spec fn spec_stmts(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss, 1nat,
{
    match spec_stmts_seq(ss, all, env, ps, sd) {
        Err(r) => Err(r),
        Ok(ds) => spec_with_end(ds, spec_block_end(ss, all, ps, sd), spec_last_place(ss)),
    }
}

/// The statements `ds` of a block, then what runs at its end.
pub open spec fn spec_with_end(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32) -> Result<DStmts, Refusal> {
    match end {
        Err(r) => Err(r),
        Ok(None) => Ok(ds),
        Ok(Some(d)) => Ok(spec_append(ds, List::Cons((Box::new(d), place), Box::new(List::Nil)))),
    }
}

/// What runs at the end of a block is the destructors, which are no statement of C++.
pub proof fn lemma_block_end_dtors(ss: Stmts, all: Fns, ps: Params, sd: Structs)
    ensures
        spec_block_end(ss, all, ps, sd) matches Ok(Some(d)) ==> d is Dtors,
{
}

pub proof fn lemma_with_end_count(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32)
    requires
        end is Ok,
        end matches Ok(Some(d)) ==> d is Dtors,
    ensures
        count_dstmts(spec_with_end(ds, end, place).unwrap()) == count_dstmts(ds),
{
    if let Ok(Some(d)) = end {
        let tail: DStmts = List::Cons((Box::new(d), place), Box::new(List::Nil));
        lemma_count_append(ds, tail);
        assert(d is Dtors);
        assert(count_dstmt(d) == 0);
        reveal_with_fuel(count_dstmts, 2);
        assert(count_dstmts(tail) == 0);
    }
}

pub proof fn lemma_with_end_resolves(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32, all: Fns, sd: Structs)
    requires
        end is Ok,
        calls_resolve(ds, all, sd),
        end matches Ok(Some(d)) ==> calls_resolve(List::Cons((Box::new(d), place), Box::new(List::Nil)), all, sd),
    ensures
        calls_resolve(spec_with_end(ds, end, place).unwrap(), all, sd),
{
    if let Ok(Some(d)) = end {
        lemma_resolve_append(ds, List::Cons((Box::new(d), place), Box::new(List::Nil)), all, sd);
    }
}

pub open spec fn spec_stmts_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss, 0nat,
{
    match ss {
        List::Nil => Ok(List::Nil),
        // The writes of each statement are checked first, decision 0177.
        List::Cons(s, rest) => match spec_write_check(*s, all, ps, sd) {
            Some(r) => Err(r),
            None => match spec_stmt(*s, all, env, ps, sd) {
                Ok(d) => match spec_stmts_seq(*rest, all, spec_scope(*s, env), ps, sd) {
                    Ok(dr) => Ok(List::Cons((Box::new(d), spec_place(*s)), Box::new(dr))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
        },
    }
}

/// An expression names `result`.
pub open spec fn spec_has_result(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Result => true,
        Expr::Finite(a) => spec_has_result(*a),
        Expr::Abs(a) => spec_has_result(*a),
        Expr::Bin(_, a, b) => spec_has_result(*a) || spec_has_result(*b),
        Expr::Not(a) => spec_has_result(*a),
        Expr::Neg(a) => spec_has_result(*a),
        Expr::Paren(a) => spec_has_result(*a),
        Expr::Size(a) => spec_has_result(*a),
        Expr::Back(a) => spec_has_result(*a),
        Expr::Empty(a) => spec_has_result(*a),
        Expr::Apply(_, args) => spec_has_result_args(*args),
        Expr::MApply(o, _, args) => spec_has_result(*o) || spec_has_result_args(*args),
        Expr::Index(a, i) => spec_has_result(*a) || spec_has_result(*i),
        Expr::Suffix(a, i) => spec_has_result(*a) || spec_has_result(*i),
        Expr::Prefix(a, j) => spec_has_result(*a) || spec_has_result(*j),
        Expr::Slice(a, i, j) => spec_has_result(*a) || spec_has_result(*i) || spec_has_result(*j),
        Expr::Forall(_, a) => spec_has_result(*a),
        Expr::Exists(_, a) => spec_has_result(*a),
        Expr::Field(a, _) => spec_has_result(*a),
        Expr::HasValue(a) => spec_has_result(*a),
        Expr::Value(a) => spec_has_result(*a),
        Expr::Chain(_, _, a, b, c) => spec_has_result(*a) || spec_has_result(*b) || spec_has_result(*c),
        Expr::Old(a) => spec_has_result(*a),
        Expr::Cond(c, a, b) => spec_has_result(*c) || spec_has_result(*a) || spec_has_result(*b),
        _ => false,
    }
}

pub open spec fn spec_has_result_args(args: Args) -> bool
    decreases args,
{
    match args {
        List::Nil => false,
        List::Cons(a, rest) => spec_has_result(*a) || spec_has_result_args(*rest),
    }
}

/// The lines of one kind of the contract of a function, in their order. A word with no rule, or a line the shell could not read,
/// is refused. A `decreases` line is the measure of a recursion, and it names no `result`, decision 0072. Each kind reads its view
/// of the object, decision 0096.
pub open spec fn spec_conds(cs: Conds, want: CondKind, ps: Params, ret: Ty, sd: Structs) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((k, e, l, decl), rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            // The pass of decision 0173 consumes each reads line that names a global.
            CondKind::Reads => Err(Refusal::Construct(READS_NAME, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Invariant => Err(Refusal::Misplaced(l)),
            CondKind::Index => Err(Refusal::Misplaced(l)),
            _ => match spec_conds(*rest, want, ps, ret, sd) {
                Ok(dr) => if k == want && k == CondKind::Decreases && spec_has_result(e) {
                    Err(Refusal::Syntax(l))
                } else if k == want {
                    match spec_contract(e, decl, spec_view_ps(ps, k), Some(spec_view_ret(ret, k)), List::Nil, l, sd) {
                        Ok(d) => Ok(List::Cons((d, l), Box::new(dr))),
                        Err(r) => Err(r),
                    }
                } else {
                    Ok(dr)
                },
                Err(r) => Err(r),
            },
        },
    }
}

/// Each name is declared once in a function, decision 0058. `seen` holds the names declared before, in the order of the source.
/// Each rule gives the first name declared a second time, with the line of that declaration, and the names seen after it.
pub open spec fn spec_twice_params(seen: Seq<u32>, ps: Params, line: u32) -> (Option<(u32, u32)>, Seq<u32>)
    decreases ps,
{
    match ps {
        List::Nil => (None, seen),
        List::Cons((n, _), rest) => if seen.contains(n) {
            (Some((n, line)), seen)
        } else {
            spec_twice_params(seen.push(n), *rest, line)
        },
    }
}

pub open spec fn spec_twice_stmt(seen: Seq<u32>, s: Stmt) -> (Option<(u32, u32)>, Seq<u32>)
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, l) => if seen.contains(n) {
            (Some((n, l)), seen)
        } else {
            (None, seen.push(n))
        },
        Stmt::If(_, t, f, _) => {
            let (r, after) = spec_twice_stmts(seen, *t);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_stmts(after, *f)
            }
        },
        Stmt::While(_, _, body, _) => spec_twice_stmts(seen, *body),
        Stmt::Block(b, _) => spec_twice_stmts(seen, *b),
        Stmt::Switch(_, _, cs, _) => spec_twice_cases(seen, *cs),
        Stmt::For(init, _, step, _, body, _) => {
            let (r, after) = spec_twice_stmt(seen, *init);
            if r.is_some() {
                (r, after)
            } else {
                let (r2, after2) = spec_twice_stmt(after, *step);
                if r2.is_some() {
                    (r2, after2)
                } else {
                    spec_twice_stmts(after2, *body)
                }
            }
        },
        // The index of a range-for is a name of the function, so a later local cannot take it, decision 0143. An index that is
        // already a name is refused by the translation of the loop, with its own sentence.
        Stmt::RangeFor(fresh, x, _, _, lc, body, l) => {
            let seen1 = match spec_index_of(*lc, fresh) {
                Ok((i, _)) => if seen.contains(i) {
                    seen
                } else {
                    seen.push(i)
                },
                Err(_) => seen,
            };
            if seen1.contains(x) {
                (Some((x, l)), seen1)
            } else {
                spec_twice_stmts(seen1.push(x), *body)
            }
        },
        _ => (None, seen),
    }
}

pub open spec fn spec_twice_stmts(seen: Seq<u32>, ss: Stmts) -> (Option<(u32, u32)>, Seq<u32>)
    decreases ss,
{
    match ss {
        List::Nil => (None, seen),
        List::Cons(s, rest) => {
            let (r, after) = spec_twice_stmt(seen, *s);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_stmts(after, *rest)
            }
        },
    }
}

pub open spec fn spec_twice_cases(seen: Seq<u32>, cs: Cases) -> (Option<(u32, u32)>, Seq<u32>)
    decreases cs,
{
    match cs {
        List::Nil => (None, seen),
        List::Cons((_, body), rest) => {
            let (r, after) = spec_twice_stmts(seen, *body);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_cases(after, *rest)
            }
        },
    }
}

/// The first name of a function declared twice: among the parameters, then among the parameters and the locals.
pub open spec fn spec_twice(f: Function) -> Option<(u32, u32)> {
    let (r, after) = spec_twice_params(Seq::empty(), f.params, f.line);
    if r.is_some() {
        r
    } else {
        spec_twice_stmts(after, f.body).0
    }
}

/// The first `return` that does not fit the result type: `return;` in a function that gives a value, or a `return` of a value in a
/// `void` function, decision 0096.
pub open spec fn spec_misreturn(ss: Stmts, void: bool) -> Option<u32>
    decreases ss,
{
    match ss {
        List::Nil => None,
        List::Cons(s, rest) => match spec_misreturn_stmt(*s, void) {
            Some(l) => Some(l),
            None => spec_misreturn(*rest, void),
        },
    }
}

pub open spec fn spec_misreturn_cases(cs: Cases, void: bool) -> Option<u32>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => match spec_misreturn(*body, void) {
            Some(l) => Some(l),
            None => spec_misreturn_cases(*rest, void),
        },
    }
}

pub open spec fn spec_misreturn_stmt(s: Stmt, void: bool) -> Option<u32>
    decreases s,
{
    match s {
        Stmt::Exit(l) => if void {
            None
        } else {
            Some(l)
        },
        Stmt::Return(_, l) => if void {
            Some(l)
        } else {
            None
        },
        Stmt::If(_, t, f, _) => match spec_misreturn(*t, void) {
            Some(l) => Some(l),
            None => spec_misreturn(*f, void),
        },
        Stmt::While(_, _, body, _) => spec_misreturn(*body, void),
        Stmt::Switch(_, _, cs, _) => spec_misreturn_cases(*cs, void),
        Stmt::For(init, _, step, _, body, _) => match spec_misreturn_stmt(*init, void) {
            Some(l) => Some(l),
            None => match spec_misreturn_stmt(*step, void) {
                Some(l) => Some(l),
                None => spec_misreturn(*body, void),
            },
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => spec_misreturn(*body, void),
        _ => None,
    }
}

/// The names that a body moves outside a `return`, at any depth, in their order, decision 0186. A move stands only at the start
/// value of a local, in a call that stands alone and in a write through a unique_ptr, so these are the only places to look.
pub open spec fn spec_moves_stmts(ss: Stmts) -> Names
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_moves_stmt(*s), spec_moves_stmts(*rest)),
    }
}

pub open spec fn spec_moves_stmt(s: Stmt) -> Names
    decreases s,
{
    match s {
        Stmt::Local(_, _, e, _) => spec_unmove(e).1,
        Stmt::Call(_, _, args, _) => spec_unmove_args(*args).1,
        Stmt::SetOwnField(_, _, e, _) => spec_unmove(e).1,
        Stmt::If(_, t, f, _) => spec_append(spec_moves_stmts(*t), spec_moves_stmts(*f)),
        Stmt::While(_, _, body, _) => spec_moves_stmts(*body),
        Stmt::For(init, _, step, _, body, _) => spec_append(spec_moves_stmt(*init), spec_append(spec_moves_stmt(*step), spec_moves_stmts(*body))),
        Stmt::Switch(_, _, cs, _) => spec_moves_cases(*cs),
        Stmt::RangeFor(_, _, _, _, _, body, _) => spec_moves_stmts(*body),
        Stmt::Block(b, _) => spec_moves_stmts(*b),
        _ => List::Nil,
    }
}

pub open spec fn spec_moves_cases(cs: Cases) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_moves_stmts(*body), spec_moves_cases(*rest)),
    }
}

/// The parameters among `ps` that are locals of the body, by their names and Dafny types: a unique_ptr that the body moves,
/// decision 0186, and each vector by value, decision 0194.
pub open spec fn spec_moved_params(ps: Params, ms: Names) -> List<(u32, DTy)>
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Own(s) => if spec_has(ms, n) {
                List::Cons((n, DTy::Opt(s)), Box::new(spec_moved_params(*rest, ms)))
            } else {
                spec_moved_params(*rest, ms)
            },
            Ty::Vec(s) => List::Cons((n, DTy::Seq(s)), Box::new(spec_moved_params(*rest, ms))),
            _ => spec_moved_params(*rest, ms),
        },
    }
}

/// The parameters among `ps` that stay parameters of the body: each one but a unique_ptr that the body moves, decision 0186, and
/// a vector by value, decision 0194.
pub open spec fn spec_kept_params(ps: Params, ms: Names) -> Params
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if ((t is Own) && spec_has(ms, n)) || (t is Vec) {
            spec_kept_params(*rest, ms)
        } else {
            List::Cons((n, t), Box::new(spec_kept_params(*rest, ms)))
        },
    }
}

/// `var p: T := p;` for each parameter that is a local of the body, at the line of the function, then `tail`, decisions 0186 and
/// 0194.
pub open spec fn spec_param_locals(mp: List<(u32, DTy)>, line: u32, tail: DStmts) -> DStmts
    decreases mp,
{
    match mp {
        List::Nil => tail,
        List::Cons((n, dt), rest) => List::Cons((Box::new(DStmt::Local(n, dt, DExpr::Var(n))), line), Box::new(spec_param_locals(*rest, line, tail))),
    }
}

/// The body with a local for each moved parameter. The body is a block, so Dafny reads each name in it as the local, and a contract
/// reads the parameter. A body that moves no parameter stays as it is, decision 0186.
pub open spec fn spec_param_block(mp: List<(u32, DTy)>, line: u32, body: DStmts) -> DStmts {
    match mp {
        List::Nil => body,
        _ => List::Cons((Box::new(DStmt::Scope(Box::new(spec_param_locals(mp, line, body)))), line), Box::new(List::Nil)),
    }
}

/// The contract and the body of a function whose signature is in the subset: the requires lines, the ensures lines, the decreases
/// lines and the body. A trusted function has no body, decision 0102.
pub open spec fn spec_inside(f: Function, all: Fns, sd: Structs) -> Result<(DConds, DConds, DConds, DStmts), Refusal> {
    match spec_conds(f.conds, CondKind::Requires, f.params, f.ret, sd) {
        Err(r) => Err(r),
        Ok(req) => match spec_conds(f.conds, CondKind::Ensures, f.params, f.ret, sd) {
            Err(r) => Err(r),
            Ok(ens) => match spec_conds(f.conds, CondKind::Decreases, f.params, f.ret, sd) {
                Err(r) => Err(r),
                Ok(dec) => if f.trusted {
                    Ok((req, ens, dec, List::Nil))
                } else {
                    match spec_twice(f) {
                    Some((n, l)) => Err(Refusal::Twice(n, l)),
                    None => match spec_misreturn(f.body, f.ret == Ty::Void) {
                        Some(l) => Err(Refusal::Syntax(l)),
                        // A unique_ptr parameter that the body moves is a local of the body, decision 0186.
                        None => match spec_stmts(f.body, all, f.params, spec_kept_params(f.params, spec_moves_stmts(f.body)), sd) {
                            Err(r) => Err(r),
                            Ok(body) => Ok((req, ens, dec, spec_param_block(spec_moved_params(f.params, spec_moves_stmts(f.body)), f.line, body))),
                        },
                    },
                    }
                },
            },
        },
    }
}

/// The requires lines `tail`, after one for each sequence parameter of fixed extent: its length is the extent, decision 0070. The
/// type `Vec` holds the bound on any other length, decision 0076.
pub open spec fn spec_bounds(ps: Params, line: u32, tail: DConds) -> DConds
    decreases ps,
{
    match ps {
        List::Nil => tail,
        List::Cons((n, t), rest) => match t {
            Ty::Seq(_, Extent::Fixed(k)) => List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(n)))), Box::new(DExpr::Lit(k))), line), Box::new(spec_bounds(*rest, line, tail))),
            _ => spec_bounds(*rest, line, tail),
        },
    }
}

/// The body of the Dafny function of a member function: the expression of its one `return`, when the function has `this` and its
/// body is that `return` alone, decision 0090. A `return` of a call is a `ReturnCall`, so a pure body holds no call. A function that
/// writes a reference parameter is never pure, decision 0108.
/// The value of a body of apply lines and one return: the value of the return after each lemma, in order, decision 0167. A local
/// before the return is a `var` of the value, decision 0172. A call of a const virtual function of an interface as the value of the
/// return or of a local is the function of the interface, whose method gives the same value, decision 0166. So is a call of a plain
/// member function that the table `sd` marks pure, decision 0189.
pub open spec fn spec_pure_value(body: DStmts, all: Fns, sd: Structs) -> Option<DExpr>
    decreases body,
{
    match body {
        List::Cons((s, _), rest) => match *s {
            DStmt::Return(d) => if *rest == List::Nil {
                Some(d)
            } else {
                None
            },
            DStmt::ReturnCall(k, da) => if *rest == List::Nil && spec_inline(all, k, sd) {
                Some(DExpr::FCall(k, Box::new(da)))
            } else {
                None
            },
            DStmt::Apply(f, da) => match spec_pure_value(*rest, all, sd) {
                Some(e) => Some(DExpr::Lemma(f, Box::new(da), Box::new(e))),
                None => None,
            },
            DStmt::Local(n, dt, d) => match spec_pure_value(*rest, all, sd) {
                Some(e) => Some(DExpr::Let(n, dt, Box::new(d), Box::new(e))),
                None => None,
            },
            DStmt::LocalCall(n, dt, k, da) => if spec_inline(all, k, sd) {
                match spec_pure_value(*rest, all, sd) {
                    Some(e) => Some(DExpr::Let(n, dt, Box::new(DExpr::FCall(k, Box::new(da))), Box::new(e))),
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        },
        List::Nil => None,
    }
}

/// A member function with `this`, or a static member function, `stat`, that writes nothing, has the value of its pure body as its
/// function, decisions 0090 and 0174. A free function never has one.
pub open spec fn spec_pure_body(ps: Params, body: DStmts, all: Fns, sd: Structs, stat: bool) -> Option<DExpr> {
    if (spec_this(ps) is Some || stat) && !spec_mutates(ps) {
        spec_pure_value(body, all, sd)
    } else {
        None
    }
}

/// The function with the key `k` is a member of a struct of the file and has no object, so it is a static member function,
/// decision 0174.
pub open spec fn spec_static_key(sd: Structs, k: u32) -> bool
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => spec_member_key(ms, k) || spec_static_key(*rest, k),
    }
}

pub open spec fn spec_member_key(ms: Members, k: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (key, _)), rest) => key == k || spec_member_key(*rest, k),
    }
}

pub fn static_key(sd: &Structs, k: u32) -> (r: bool)
    ensures
        r == spec_static_key(*sd, k),
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => member_key(ms, k) || static_key(rest, k),
    }
}

pub fn member_key(ms: &Members, k: u32) -> (r: bool)
    ensures
        r == spec_member_key(*ms, k),
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (key, _)), rest) => *key == k || member_key(rest, k),
    }
}

/// The parameters as arguments, each by its name.
pub open spec fn spec_param_args(ps: Params) -> DArgs
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((p, _), rest) => List::Cons(DExpr::Var(p), Box::new(spec_param_args(*rest))),
    }
}

/// The ensures lines of a method, and for a pure member function one more: `result == F(params)`, at the line of the function.
pub open spec fn spec_linked(f: Function, ens: DConds, pure: Option<DExpr>) -> DConds {
    match pure {
        Some(_) => spec_link(f, ens),
        None => if spec_const_virtual(f) {
            // The method of a virtual function gives the value of its function, decision 0166.
            spec_link(f, ens)
        } else {
            ens
        },
    }
}

/// The interface of a virtual function: its first parameter is `this` of it, decision 0165.
pub open spec fn spec_virtual(f: Function) -> Option<u32> {
    match spec_head_ty(f.params) {
        Some(Ty::Iface(k)) => Some(k),
        Some(Ty::IfaceMut(k)) => Some(k),
        _ => None,
    }
}

/// A virtual function that does not write its object: a function of the model, decision 0166.
pub open spec fn spec_const_virtual(f: Function) -> bool {
    spec_head_ty(f.params) is Some && spec_head_ty(f.params)->Some_0 is Iface
}

/// Each member marked as no function in the model.
pub open spec fn spec_unmark(ms: Members) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, _)), rest) => List::Cons((n, (k, None)), Box::new(spec_unmark(*rest))),
    }
}

/// The members, with the member of the function `key` and each one after it marked as no function in the model.
pub open spec fn spec_from(ms: Members, key: u32) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, p)), rest) => if k == key {
            spec_unmark(ms)
        } else {
            List::Cons((n, (k, p)), Box::new(spec_from(*rest, key)))
        },
    }
}

/// The table that a contract of the virtual function `key` of the interface `b` reads: only the functions above it in `b` are
/// functions of the model, decision 0166.
pub open spec fn spec_above(sd: Structs, b: u32, key: u32) -> Structs
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => if k == b {
            List::Cons((k, (l, fields, spec_from(ms, key))), Box::new(spec_above(*rest, b, key)))
        } else {
            List::Cons((k, (l, fields, ms)), Box::new(spec_above(*rest, b, key)))
        },
    }
}

/// The table that the contract of `f` reads. A virtual function has no body, so the table reads only its contract.
pub open spec fn spec_view_of(f: Function, sd: Structs) -> Structs {
    match spec_virtual(f) {
        Some(b) => if f.trusted {
            spec_above(sd, b, f.name)
        } else {
            sd
        },
        None => sd,
    }
}

/// The name of the member of the function `key`.
pub open spec fn spec_member_name(ms: Members, key: u32) -> Option<u32>
    decreases ms,
{
    match ms {
        List::Nil => None,
        List::Cons((n, (k, _)), rest) => if k == key {
            Some(n)
        } else {
            spec_member_name(*rest, key)
        },
    }
}

/// The first member of the name `g` is the member of the function `key` or comes after it.
pub open spec fn spec_at_or_after(ms: Members, key: u32, g: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((n, (k, _)), rest) => if k == key {
            spec_get(ms, g) is Some
        } else if n == g {
            false
        } else {
            spec_at_or_after(*rest, key, g)
        },
    }
}

/// Each member of `ms` from the one of the function `key` on is no function in the model of `spec_from`.
pub proof fn lemma_from_unmarks(ms: Members, key: u32, g: u32)
    requires
        spec_at_or_after(ms, key, g),
    ensures
        match spec_get(spec_from(ms, key), g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((_, (k, _)), rest) => if k == key {
            lemma_unmark_none(ms, g);
        } else {
            lemma_from_unmarks(*rest, key, g);
        },
    }
}

proof fn lemma_unmark_none(ms: Members, g: u32)
    requires
        spec_get(ms, g) is Some,
    ensures
        match spec_get(spec_unmark(ms), g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((n, _), rest) => if n != g {
            lemma_unmark_none(*rest, g);
        },
    }
}

/// A contract of a virtual function reads no function of its interface at or after it as a function of the model, decision 0166.
/// So the functions of the model of an interface call each other in the order of the interface, with no cycle.
pub proof fn lemma_a_later_function_is_no_function(sd: Structs, b: u32, key: u32, g: u32)
    requires
        match spec_get(sd, b) {
            Some((_, _, ms)) => spec_at_or_after(ms, key, g),
            None => false,
        },
    ensures
        match spec_member(spec_above(sd, b, key), b, g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases sd,
{
    match sd {
        List::Nil => {},
        List::Cons((k, (_, _, ms)), rest) => if k == b {
            lemma_from_unmarks(ms, key, g);
        } else {
            lemma_a_later_function_is_no_function(*rest, b, key, g);
        },
    }
}

/// The refusal of a contract of `f`. A virtual function that reads a later function of its interface gets `Later`, decision 0166.
pub open spec fn spec_late(f: Function, sd: Structs, r: Refusal) -> Refusal {
    match spec_virtual(f) {
        Some(b) => match r {
            Refusal::NotPure(g, l) => match spec_get(sd, b) {
                Some((_, _, ms)) => if spec_at_or_after(ms, f.name, g) {
                    match spec_member_name(ms, f.name) {
                        Some(n) => Refusal::Later(b, n, g, l),
                        None => r,
                    }
                } else {
                    r
                },
                None => r,
            },
            _ => r,
        },
        None => r,
    }
}

/// The contract and the body of `f` under the table that its contract reads, decision 0166.
pub open spec fn spec_inside_of(f: Function, all: Fns, sd: Structs) -> Result<(DConds, DConds, DConds, DStmts), Refusal> {
    match spec_inside(f, all, spec_view_of(f, sd)) {
        Ok(x) => Ok(x),
        Err(r) => Err(spec_late(f, sd, r)),
    }
}

/// The ensures lines of a method with one more: `result == F(params)`, at the line of the function.
pub open spec fn spec_link(f: Function, ens: DConds) -> DConds {
    spec_append(
        ens,
        List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(spec_param_args(f.params))))), f.line), Box::new(List::Nil)),
    )
}


/// The member `name` of the struct `k`: the key of its function, and its return type when it is pure.
pub open spec fn spec_member(sd: Structs, k: u32, name: u32) -> Option<(u32, Option<(Ty, Params)>)> {
    match spec_get(sd, k) {
        Some((_, _, ms)) => spec_get(ms, name),
        None => None,
    }
}

/// The key of the struct of a type of a path: a struct, or the object `this`.
pub open spec fn spec_struct_key(t: Ty) -> Option<u32> {
    match t {
        Ty::Struct(k) => Some(k),
        Ty::This(k) => Some(k),
        Ty::ThisMut(k) => Some(k),
        Ty::ThisAfter(k) => Some(k),
        // An interface has no field, and its member functions are its virtual functions, decision 0166.
        Ty::Iface(k) => Some(k),
        Ty::IfaceRef(k) => Some(k),
        Ty::IfaceMut(k) => Some(k),
        _ => None,
    }
}

/// The function of the file with the key `key`.
pub open spec fn spec_find(fs: Fns, key: u32) -> Option<Function>
    decreases fs,
{
    match fs {
        List::Nil => None,
        List::Cons(f, rest) => if f.name == key {
            Some(*f)
        } else {
            spec_find(*rest, key)
        },
    }
}

/// The return type and parameters of the function with the key `key`, when it is a pure member function with a signature of the
/// subset. When `strict` holds, its contract must also have a model under the table `sd`, decision 0095. A trusted member is never
/// pure, decision 0102.
pub open spec fn spec_pure_ret(all: Fns, key: u32, sd: Structs, strict: bool) -> Option<(Ty, Params)> {
    match spec_find(all, key) {
        Some(f) => if !has_signature(f, sd) {
            None
        } else if spec_const_virtual(f) {
            // A virtual function is a function of the model with no body, decision 0166.
            if !strict {
                Some((f.ret, f.params))
            } else {
                match spec_inside_of(f, all, sd) {
                    Ok(_) => Some((f.ret, f.params)),
                    Err(_) => None,
                }
            }
        } else if f.trusted {
            None
        } else if strict {
            match spec_inside(f, all, sd) {
                Ok((_, _, _, body)) => match spec_pure_body(f.params, body, all, sd, spec_static_key(sd, f.name)) {
                    Some(_) => Some((f.ret, f.params)),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match spec_stmts(f.body, all, f.params, f.params, sd) {
                Ok(body) => match spec_pure_body(f.params, body, all, sd, spec_static_key(sd, f.name)) {
                    Some(_) => Some((f.ret, f.params)),
                    None => None,
                },
                Err(_) => None,
            }
        },
        None => None,
    }
}

pub open spec fn spec_mark_members(ms: Members, all: Fns, sd: Structs, strict: bool) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((n, (key, spec_member_mark(all, key, sd, strict))), Box::new(spec_mark_members(*rest, all, sd, strict))),
    }
}

/// The mark of the member with the key `key`: its type and parameters when it is pure. A member with no function of the file, as a
/// member of a class template that no instance makes, has the type `Other` of its key, which no pure member has, decision 0188.
pub open spec fn spec_member_mark(all: Fns, key: u32, sd: Structs, strict: bool) -> Option<(Ty, Params)> {
    if spec_find(all, key) is None {
        Some((Ty::Other(key), List::Nil))
    } else {
        spec_pure_ret(all, key, sd, strict)
    }
}

/// The table `t` with each member marked pure or not from the functions of the file, whatever the table said, decision 0090.
/// `sd` is the table that the marks read.
pub open spec fn spec_mark(t: Structs, all: Fns, sd: Structs, strict: bool) -> Structs
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => List::Cons((k, (l, fields, spec_mark_members(ms, all, sd, strict))), Box::new(spec_mark(*rest, all, sd, strict))),
    }
}

/// The table of the unit: first the members whose body is pure, then of those the members whose contract also has a model under
/// that first table, decision 0095. A contract that calls a member reads the second table.
pub open spec fn spec_marked(sd: Structs, all: Fns) -> Structs {
    spec_settle(sd, all, spec_top(sd, all), spec_all_members(sd))
}

/// The table with each member marked pure, as its signature says, and each member with no function marked as such. The marks of
/// the unit come down from it, decision 0190.
pub open spec fn spec_top(t: Structs, all: Fns) -> Structs
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => List::Cons((k, (l, fields, spec_top_members(ms, all))), Box::new(spec_top(*rest, all))),
    }
}

pub open spec fn spec_top_members(ms: Members, all: Fns) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((n, (key, spec_top_mark(all, key))), Box::new(spec_top_members(*rest, all))),
    }
}

pub open spec fn spec_top_mark(all: Fns, key: u32) -> Option<(Ty, Params)> {
    match spec_find(all, key) {
        Some(f) => Some((f.ret, f.params)),
        None => Some((Ty::Other(key), List::Nil)),
    }
}

/// The members of each struct of the table, in order. Their count bounds the passes of the marks.
pub open spec fn spec_all_members(t: Structs) -> Members
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((_, (_, _, ms)), rest) => spec_append(ms, spec_all_members(*rest)),
    }
}

/// The strict marks, from the table `t`, until a pass marks no member other than `t` does. A member keeps its mark only when its
/// body is pure and its contract has a model under the marks before. Each pass takes marks away, never adds one, so there is one
/// pass at most for each member of `ks`, and the marks then hold of their own table. So a call of a plain member function in a body
/// reads the same marks as a contract that calls its caller, decisions 0189 and 0190.
/// ponytail: the core does not prove that a pass only takes marks away, nor that the result holds of its own table, and the last
/// pass at the bound is not checked. A break shows as a call of a function that the model does not define, which Dafny refuses.
/// The upgrade is a lemma that spec_mark is monotone in its table, and from it a lemma that each FCall key of spec_unit names a
/// model whose function is Some.
pub open spec fn spec_settle(sd: Structs, all: Fns, t: Structs, ks: Members) -> Structs
    decreases ks,
{
    match ks {
        List::Nil => spec_mark(sd, all, t, true),
        List::Cons(_, rest) => if spec_same_marks(spec_mark(sd, all, t, true), t) {
            t
        } else {
            spec_settle(sd, all, spec_mark(sd, all, t, true), *rest)
        },
    }
}

/// Two tables of one shape mark the same members.
pub open spec fn spec_same_marks(a: Structs, b: Structs) -> bool
    decreases a,
{
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons((_, (_, _, ma)), ra), List::Cons((_, (_, _, mb)), rb)) => spec_same_member_marks(ma, mb) && spec_same_marks(*ra, *rb),
        _ => false,
    }
}

pub open spec fn spec_same_member_marks(a: Members, b: Members) -> bool
    decreases a,
{
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons((_, (_, x)), ra), List::Cons((_, (_, y)), rb)) => (x is Some) == (y is Some) && spec_same_member_marks(*ra, *rb),
        _ => false,
    }
}

} // verus!

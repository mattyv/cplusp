//! The translator: properties of the rules. The summary of the proofs is in `model`.

#[allow(unused_imports)]
use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ properties of the rules

pub open spec fn unknown_expr(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Unknown(_, _) => true,
        Expr::Finite(a) => unknown_expr(*a),
        Expr::Abs(a) => unknown_expr(*a),
        Expr::Bin(_, a, b) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Not(a) => unknown_expr(*a),
        Expr::Neg(a) => unknown_expr(*a),
        Expr::Cast(_, a) => unknown_expr(*a),
        Expr::Paren(a) => unknown_expr(*a),
        Expr::Brace(a) => unknown_expr(*a),
        Expr::Call(_, _, args, _) => unknown_args(*args),
        Expr::Size(a) => unknown_expr(*a),
        Expr::Back(a) => unknown_expr(*a),
        Expr::Index(a, i) => unknown_expr(*a) || unknown_expr(*i),
        Expr::CountIf(a, _, _, t) => unknown_expr(*a) || unknown_expr(*t),
        Expr::Copy(a, _, _) => unknown_expr(*a),
        Expr::Field(a, _) => unknown_expr(*a),
        Expr::Construct(_, args) => unknown_args(*args),
        Expr::Forall(_, a) => unknown_expr(*a),
        Expr::Exists(_, a) => unknown_expr(*a),
        Expr::Chain(_, _, a, b, c) => unknown_expr(*a) || unknown_expr(*b) || unknown_expr(*c),
        Expr::HasValue(a) => unknown_expr(*a),
        Expr::Value(a) => unknown_expr(*a),
        Expr::Wrap(a) => unknown_expr(*a),
        Expr::Empty(a) => unknown_expr(*a),
        Expr::Subspan(a, k) => unknown_expr(*a) || unknown_expr(*k),
        Expr::Apply(_, args) => unknown_args(*args),
        Expr::MApply(o, _, args) => unknown_expr(*o) || unknown_args(*args),
        Expr::Suffix(a, i) => unknown_expr(*a) || unknown_expr(*i),
        Expr::Prefix(a, j) => unknown_expr(*a) || unknown_expr(*j),
        Expr::Slice(a, i, j) => unknown_expr(*a) || unknown_expr(*i) || unknown_expr(*j),
        Expr::Divide(_, a, b, _) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Shr(a, b, _) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Bits(_, a, b, _) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Fill(a, b) => unknown_expr(*a) || unknown_expr(*b),
        Expr::StaticCast(_, a) => unknown_expr(*a),
        Expr::List(args) => unknown_args(*args),
        Expr::Step(_, _, _, _) => false,
        Expr::Old(a) => unknown_expr(*a),
        Expr::Cond(c, a, b) => unknown_expr(*c) || unknown_expr(*a) || unknown_expr(*b),
        _ => false,
    }
}

pub open spec fn unknown_args(args: Args) -> bool
    decreases args,
{
    match args {
        List::Nil => false,
        List::Cons(a, rest) => unknown_expr(*a) || unknown_args(*rest),
    }
}

pub open spec fn unknown_stmt(s: Stmt) -> bool
    decreases s,
{
    match s {
        Stmt::Unknown(_, _) => true,
        Stmt::Return(e, _) => unknown_expr(e),
        Stmt::If(c, t, f, _) => unknown_expr(c) || unknown_stmts(*t) || unknown_stmts(*f),
        Stmt::Local(_, _, e, _) => unknown_expr(e),
        Stmt::Assign(_, e, _) => unknown_expr(e),
        Stmt::Step(_, _, _, _) => false,
        Stmt::While(c, _, body, _) => unknown_expr(c) || unknown_stmts(*body),
        Stmt::For(init, c, step, _, body, _) => unknown_stmt(*init) || unknown_expr(c) || unknown_stmt(*step) || unknown_stmts(*body),
        Stmt::RangeFor(_, _, _, seq, _, body, _) => unknown_expr(seq) || unknown_stmts(*body),
        Stmt::SetField(_, e, _) => unknown_expr(e),
        Stmt::SetRefField(_, _, e, _) => unknown_expr(e),
        Stmt::SetOwnField(_, _, e, _) => unknown_expr(e),
        Stmt::SetIndex(_, i, e, _) => unknown_expr(i) || unknown_expr(e),
        Stmt::SetFieldAt(_, i, e, _) => unknown_expr(i) || unknown_expr(e),
        Stmt::PushField(_, e, _) => unknown_expr(e),
        Stmt::SetThroughField(_, _, e, _) => unknown_expr(e),
        Stmt::PopField(_, _) => false,
        Stmt::PushBack(_, e, _) => unknown_expr(e),
        Stmt::Sort(_, _) => false,
        Stmt::SortBy(_, _, _, _, e, _) => unknown_expr(e),
        Stmt::Switch(e, _, cs, _) => unknown_expr(e) || unknown_cases(*cs),
        Stmt::Call(_, _, args, _) => unknown_args(*args),
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
        Stmt::Block(b, _) => unknown_stmts(*b),
    }
}

pub open spec fn unknown_cases(cs: Cases) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((_, body), rest) => unknown_stmts(*body) || unknown_cases(*rest),
    }
}

pub open spec fn unknown_stmts(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => unknown_stmt(*s) || unknown_stmts(*rest),
    }
}

pub proof fn lemma_unknown_code_is_refused(e: Expr, line: u32)
    requires
        unknown_expr(e),
    ensures
        spec_code(e, line).is_err(),
{
    lemma_unknown_lift_is_refused(e, List::Nil, line, List::Nil, 0, false);
}

/// Taking the moves out of an expression keeps each node with no rule, decision 0171.
pub proof fn lemma_unmove_unknown(e: Expr)
    ensures
        unknown_expr(e) ==> unknown_expr(spec_unmove(e).0),
        (e is Call) == (spec_unmove(e).0 is Call),
        e is Call ==> spec_unmove(e).0->Call_0 == e->Call_0 && spec_unmove(e).0->Call_1 == e->Call_1 && *spec_unmove(e).0->Call_2 == spec_unmove_args(*e->Call_2).0 && spec_unmove(e).0->Call_3 == e->Call_3,
    decreases e,
{
    match e {
        Expr::Call(_, _, args, _) => lemma_unmove_args_unknown(*args),
        Expr::Construct(_, args) => lemma_unmove_args_unknown(*args),
        Expr::Wrap(a) => lemma_unmove_unknown(*a),
        Expr::Cast(_, a) => lemma_unmove_unknown(*a),
        Expr::Paren(a) => lemma_unmove_unknown(*a),
        _ => {},
    }
}

pub proof fn lemma_unmove_args_unknown(args: Args)
    ensures
        unknown_args(args) ==> unknown_args(spec_unmove_args(args).0),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_unmove_unknown(*a);
            lemma_unmove_args_unknown(*rest);
        },
        List::Nil => {},
    }
}

pub proof fn lemma_unknown_local_call_is_refused(
    n: u32,
    dt: DTy,
    key: u32,
    name: u32,
    args: Args,
    at: u32,
    all: Fns,
    line: u32,
    ps: Params,
    sd: Structs,
)
    requires
        unknown_args(args),
    ensures
        spec_local_call(n, dt, key, name, args, at, all, line, ps, sd).is_err(),
{
    lemma_unknown_call_lift_is_refused(key, name, args, at, all, line, sd);
}

pub proof fn lemma_unknown_call_stmt_is_refused(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs)
    requires
        unknown_args(args),
    ensures
        spec_call_stmt(key, name, args, line, all, ps, sd).is_err(),
{
    lemma_unknown_call_lift_is_refused(key, name, args, line, all, line, sd);
}

/// A call that stands alone, whose arguments hold a node with no rule, is refused.
pub proof fn lemma_unknown_call_lift_is_refused(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs)
    requires
        unknown_args(args),
    ensures
        spec_call_lift(key, name, args, at, all, line, sd).is_err(),
{
    if spec_callable(all, key, sd) {
        lemma_unknown_lift_args_is_refused(args, all, line, sd, 0, true);
    }
}

/// The value of a return or of a write, with a node with no rule, is refused.
pub proof fn lemma_unknown_value_is_refused(e: Expr, all: Fns, line: u32, sd: Structs)
    requires
        unknown_expr(e),
    ensures
        e is Call ==> spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_err(),
        !(e is Call) ==> spec_lift(e, all, line, sd, 0, true).is_err(),
{
    if e is Call {
        lemma_unknown_call_lift_is_refused(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd);
    } else {
        lemma_unknown_lift_is_refused(e, all, line, sd, 0, true);
    }
}

/// A return value with a node that has no rule is refused, a braced list too, decision 0175.
pub proof fn lemma_unknown_return_is_refused(e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        unknown_expr(e),
    ensures
        spec_return(e, l, all, ps, sd).is_err(),
{
    if e is List {
        lemma_unknown_lift_args_is_refused(*e->List_0, all, l, sd, 0, true);
    } else if e is Construct {
        lemma_unknown_lift_args_is_refused(*e->Construct_1, all, l, sd, 0, true);
    } else if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_unknown_lower_is_refused(e, None, false, all, l, sd, 0);
    } else {
        lemma_unknown_value_is_refused(e, all, l, sd);
    }
}

/// A local vector `v(n, x)` that holds a node with no rule is refused, decision 0185.
pub proof fn lemma_unknown_fill_local_is_refused(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        t is Vec,
        e is Fill,
        unknown_expr(e),
    ensures
        spec_local_stmt(n, t, e, l, all, env, ps, sd).is_err(),
{
    reveal(spec_local_stmt);
    let c = *e->Fill_0;
    let x = *e->Fill_1;
    if unknown_expr(c) {
        lemma_unknown_lift_is_refused(c, all, l, sd, 0, true);
    } else if spec_lift(c, all, l, sd, 0, true).is_ok() {
        lemma_unknown_lift_is_refused(x, all, l, sd, spec_lift(c, all, l, sd, 0, true).unwrap().2, true);
    }
}

/// A local std::array from a brace list that holds a node with no rule is refused, decision 0184, and so is one from `k` copies of
/// a value, decision 0196.
pub proof fn lemma_unknown_array_local_is_refused(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        t is Seq && t->Seq_1 is Fixed,
        unknown_expr(e),
    ensures
        spec_local_stmt(n, t, e, l, all, env, ps, sd).is_err(),
{
    reveal(spec_local_stmt);
    if let Expr::List(args) = e {
        lemma_unknown_lift_args_is_refused(*args, all, l, sd, 0, true);
    }
    // `k` copies of a value, decision 0196: an unknown count is no literal, and an unknown value does not lift.
    if let Expr::Fill(c, x) = e {
        if !unknown_expr(*c) {
            lemma_unknown_lift_is_refused(*x, all, l, sd, 0, true);
        }
    }
}

#[verifier::rlimit(40)]
pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all, env, ps, sd).is_err(),
    decreases s, 0nat,
{
    match s {
        Stmt::Return(e, l) => {
            reveal(spec_return_stmt);
            lemma_unmove_unknown(e);
            lemma_unknown_return_is_refused(spec_unmove(e).0, l, all, ps, sd);
            lemma_unknown_lift_is_refused(spec_unmove(e).0, all, l, sd, 0, true);
            lemma_unknown_lower_is_refused(spec_unmove(e).0, None, true, all, l, sd, 0);
        },
        Stmt::Block(b, _) => lemma_unknown_stmts_is_refused(*b, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, true);
            } else if unknown_stmts(*t) {
                lemma_unknown_stmts_is_refused(*t, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*f, all, env, ps, sd);
            }
        },
        Stmt::Local(n, t, e, l) => if t is Seq && t->Seq_1 is Fixed {
            lemma_unknown_array_local_is_refused(n, t, e, l, all, env, ps, sd);
        } else if t is Vec && e is Fill {
            lemma_unknown_fill_local_is_refused(n, t, e, l, all, env, ps, sd);
        } else {
            reveal(spec_local_stmt);
            if e is Call {
                if let Ok(dt) = spec_value_ty(t, l, sd) {
                    lemma_unknown_local_call_is_refused(n, dt, e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, l, ps, sd);
                }
            } else {
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            }
            // The start value of a local with no vector type reads its moves first, decision 0171.
            lemma_unmove_unknown(e);
            let e2 = spec_unmove(e).0;
            if e2 is Call {
                lemma_unmove_args_unknown(*e->Call_2);
                if let Ok(dt) = spec_value_ty(t, l, sd) {
                    lemma_unknown_local_call_is_refused(n, dt, e2->Call_0, e2->Call_1, *e2->Call_2, e2->Call_3, all, l, ps, sd);
                }
            } else {
                lemma_unknown_lift_is_refused(e2, all, l, sd, 0, true);
            }
        },
        Stmt::SetField(_, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        Stmt::SetRefField(_, _, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        // The value of a write through a unique_ptr lifts after its moves, decision 0186.
        Stmt::SetOwnField(_, _, e, l) => {
            lemma_unmove_unknown(e);
            lemma_unknown_lift_is_refused(spec_unmove(e).0, all, l, sd, 0, true);
        },
        Stmt::SetIndex(_, i, e, l) => {
            if unknown_expr(i) {
                lemma_unknown_code_is_refused(i, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::SetFieldAt(_, i, e, l) => {
            if unknown_expr(i) {
                lemma_unknown_code_is_refused(i, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::PushField(_, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::SetThroughField(_, _, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::PushBack(_, e, l) => {
            lemma_unknown_code_is_refused(e, l);
            lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
        },
        Stmt::Sort(_, _) => {},
        Stmt::SortBy(_, _, _, _, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::Switch(e, _, cs, l) => {
            if unknown_expr(e) {
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            } else {
                lemma_unknown_cases_is_refused(*cs, all, env, ps, sd);
            }
        },
        Stmt::Call(k, nm, args, l) => {
            lemma_unmove_args_unknown(*args);
            lemma_unknown_call_stmt_is_refused(k, nm, spec_unmove_args(*args).0, l, all, ps, sd);
        },
        Stmt::Assign(_, e, l) => {
            reveal(spec_assign_stmt);
            lemma_unknown_value_is_refused(e, all, l, sd);
        },
        Stmt::While(c, _, body, l) => {
            if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, false);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, env, ps, sd);
            }
        },
        Stmt::For(init, c, step, _, body, l) => {
            if unknown_stmt(*init) {
                lemma_unknown_stmt_is_refused(*init, all, env, ps, sd);
            } else if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, false);
            } else if unknown_stmt(*step) {
                lemma_unknown_stmt_is_refused(*step, all, spec_scope(*init, env), ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, spec_scope(*init, env), ps, sd);
            }
        },
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => {
            if !unknown_expr(seq) {
                if let Ok((i, _)) = spec_index_of(*lc, fresh) {
                    let turn = List::Cons((x, xt), Box::new(List::Cons((i, Ty::U64), Box::new(env))));
                    lemma_unknown_stmts_is_refused(*body, all, turn, ps, sd);
                }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_cases_is_refused(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_cases(cs),
    ensures
        spec_cases(cs, all, env, ps, sd).is_err(),
    decreases cs, 0nat,
{
    match cs {
        List::Cons((_, body), rest) => {
            if unknown_stmts(*body) {
                lemma_unknown_stmts_is_refused(*body, all, env, ps, sd);
            } else {
                lemma_unknown_cases_is_refused(*rest, all, env, ps, sd);
            }
        },
        List::Nil => {},
    }
}

pub proof fn lemma_unknown_stmts_is_refused(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts(ss, all, env, ps, sd).is_err(),
    decreases ss, 1nat,
{
    lemma_unknown_stmts_is_refused_seq(ss, all, env, ps, sd);
}

pub proof fn lemma_unknown_stmts_is_refused_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts_seq(ss, all, env, ps, sd).is_err(),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused_seq(*rest, all, spec_scope(*s, env), ps, sd);
            }
        },
        List::Nil => {},
    }
}

/// A body that holds a node with no rule never gives a full model of a verified function. The translator never skips one. Only a
/// trusted function, whose body the translator does not read, has a full model then, decision 0102.
pub proof fn lemma_unknown_is_refused(f: Function, all: Fns, sd: Structs)
    requires
        unknown_stmts(f.body),
        !f.trusted,
    ensures
        !(spec_function(f, all, sd) is Full),
{
    lemma_unknown_stmts_is_refused(f.body, all, f.params, spec_kept_params(f.params, spec_moves_stmts(f.body)), sd);
}

pub open spec fn count_stmts(ss: Stmts) -> nat
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons(s, rest) => count_stmt(*s) + count_stmts(*rest),
    }
}

pub open spec fn count_stmt(s: Stmt) -> nat
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => 1 + count_stmts(*t) + count_stmts(*f),
        Stmt::While(_, _, body, _) => 1 + count_stmts(*body),
        Stmt::Block(b, _) => 1 + count_stmts(*b),
        Stmt::Switch(_, _, cs, _) => 1 + count_cases(*cs),
        Stmt::For(init, _, step, _, body, _) => 1 + count_stmt(*init) + count_stmt(*step) + count_stmts(*body),
        // The loop, the start of its index, its step and the element that starts each turn, decision 0143.
        Stmt::RangeFor(_, _, _, _, _, body, _) => 4 + count_stmts(*body),
        _ => 1,
    }
}

pub open spec fn count_cases(cs: Cases) -> nat
    decreases cs,
{
    match cs {
        List::Nil => 0,
        List::Cons((_, body), rest) => count_stmts(*body) + count_cases(*rest),
    }
}

pub open spec fn count_dcases(cs: DCases) -> nat
    decreases cs,
{
    match cs {
        List::Nil => 0,
        List::Cons((_, body), rest) => count_dstmts(*body) + count_dcases(*rest),
    }
}

pub open spec fn count_dstmts(ss: DStmts) -> nat
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons((s, _), rest) => count_dstmt(*s) + count_dstmts(*rest),
    }
}

pub open spec fn count_dstmt(s: DStmt) -> nat
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => 1 + count_dstmts(*t) + count_dstmts(*f),
        DStmt::While(_, _, _, body) => 1 + count_dstmts(*body),
        DStmt::Match(_, _, cs) => 1 + count_dcases(*cs),
        DStmt::For(init, _, _, _, _, body, step, _) => 1 + count_dstmt(*init) + count_dstmt(*step) + count_dstmts(*body),
        DStmt::Pre(_, s) => count_dstmt(*s),
        DStmt::Moved(s, _) => count_dstmt(*s),
        DStmt::Gone(s, _, _) => count_dstmt(*s),
        // A bare block is a statement with its statements, and the destructors that run at the end of a block are none, decision 0178.
        DStmt::Scope(b) => 1 + count_dstmts(*b),
        DStmt::Dtors(_) => 0,
        _ => 1,
    }
}

/// The calls before a statement add no statement.
pub proof fn lemma_pre_count(c: DCalls, s: DStmt)
    ensures
        count_dstmt(spec_pre(c, s)) == count_dstmt(s),
{
}

/// A statement that holds no statement gives one Dafny statement, with or without calls before it.
pub proof fn lemma_kept_return(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Return,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal(spec_return_stmt);
    reveal_with_fuel(count_dstmt, 2);
}

/// A statement that moves is one Dafny statement, as the statement inside it, decision 0171.
pub proof fn lemma_gone_all_count(d: DStmt, vs: Names)
    ensures
        count_dstmt(spec_gone_all(d, vs)) == count_dstmt(d),
    decreases vs,
{
    reveal_with_fuel(count_dstmt, 2);
    match vs {
        List::Nil => {},
        List::Cons(w, rest) => lemma_gone_all_count(DStmt::Gone(Box::new(d), w, false), *rest),
    }
}

pub proof fn lemma_gone_all_resolves(d: DStmt, vs: Names, all: Fns, sd: Structs)
    requires
        calls_resolve_stmt(d, all, sd),
    ensures
        calls_resolve_stmt(spec_gone_all(d, vs), all, sd),
    decreases vs,
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    match vs {
        List::Nil => {},
        List::Cons(w, rest) => lemma_gone_all_resolves(DStmt::Gone(Box::new(d), w, false), *rest, all, sd),
    }
}

/// A statement that moves resolves when the statement does.
pub proof fn lemma_moved_resolves(d: DStmt, ns: Names, vs: Names, all: Fns, sd: Structs)
    requires
        calls_resolve_stmt(d, all, sd),
    ensures
        calls_resolve_stmt(spec_moved(d, ns, vs), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    lemma_gone_all_resolves(spec_nulled(d, spec_without(ns, vs)), vs, all, sd);
}

pub proof fn lemma_moved_count(d: DStmt, ns: Names, vs: Names)
    ensures
        count_dstmt(spec_moved(d, ns, vs)) == count_dstmt(d),
{
    reveal_with_fuel(count_dstmt, 2);
    lemma_gone_all_count(spec_nulled(d, spec_without(ns, vs)), vs);
}

pub proof fn lemma_local_value_kept(n: u32, dt: DTy, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_local_value(n, dt, e, l, all, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_local_value(n, dt, e, l, all, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_call_stmt_kept(k: u32, nm: u32, args: Args, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_call_stmt(k, nm, args, l, all, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_call_stmt(k, nm, args, l, all, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_local(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Local,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal(spec_local_stmt);
    if s->Local_1 is Vec || (s->Local_1 is Seq && s->Local_1->Seq_1 is Fixed) {
        reveal_with_fuel(count_dstmt, 2);
    } else {
        let (n, t, e, l) = (s->Local_0, s->Local_1, s->Local_2, s->Local_3);
        let dt = spec_value_ty(t, l, sd).unwrap();
        let (e2, ns) = spec_unmove(e);
        lemma_local_value_kept(n, dt, e2, l, all, ps, sd);
        lemma_moved_count(spec_local_value(n, dt, e2, l, all, ps, sd).unwrap(), ns, spec_vec_moves(e));
    }
}

pub proof fn lemma_kept_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal(spec_assign_stmt);
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_set_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetField || s is SetRefField || s is SetFieldAt || s is PushField || s is PopField || s is SetThroughField || s is PushBack,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_set_own_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetOwnField,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    let (n, f, l) = (s->SetOwnField_0, s->SetOwnField_1, s->SetOwnField_3);
    let (e2, ns) = spec_unmove(s->SetOwnField_2);
    let (c, d, _) = spec_lift(e2, all, l, sd, 0, true).unwrap();
    lemma_pre_count(c, DStmt::SetOwnField(n, f, d));
    lemma_moved_count(spec_pre(c, DStmt::SetOwnField(n, f, d)), ns, spec_vec_moves(s->SetOwnField_2));
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_call(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Call,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    let (k, nm, l) = (s->Call_0, s->Call_1, s->Call_3);
    let (a2, ns) = spec_unmove_args(*s->Call_2);
    lemma_call_stmt_kept(k, nm, a2, l, all, ps, sd);
    lemma_moved_count(spec_call_stmt(k, nm, a2, l, all, ps, sd).unwrap(), ns, spec_vec_moves_args(*s->Call_2));
}


/// The variables in scope in the body of a range-for: its element, then its index, then those before the loop, decision 0143.
pub open spec fn spec_range_turn(s: Stmt, env: Params) -> Params {
    match s {
        Stmt::RangeFor(fresh, x, xt, _, lc, _, _) => List::Cons(
            (x, xt),
            Box::new(List::Cons((spec_index_of(*lc, fresh).unwrap().0, Ty::U64), Box::new(env))),
        ),
        _ => env,
    }
}

/// A range-for that translates has a body that translates in the scope of its turn.
pub proof fn lemma_range_body_ok(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).is_ok(),
{
}

/// A range-for gives one Dafny statement for the loop, the start of its index, its step and its element, and those of its body.
/// The Dafny loop of a range-for that translates, built from the parts that translate, decision 0143.
pub open spec fn spec_range_dstmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> DStmt {
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let inner = List::Cons((i, Ty::U64), Box::new(env));
                let inv = spec_loop_conds(*lc, CondKind::Invariant, inner, sd, true).unwrap();
                let dec = spec_loop_conds(*lc, CondKind::Decreases, inner, sd, true).unwrap();
                let dbound = spec_contract(spec_range_bound(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd).unwrap();
                let dmeasure = spec_contract(spec_range_measure(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd).unwrap();
                let dc = spec_code(spec_range_test(i, v, sc, ext), l).unwrap();
                let dt = spec_value_ty(xt, l, sd).unwrap();
                let de = spec_code(spec_range_elem(i, v, sc, ext), l).unwrap();
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                DStmt::For(
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
                )
            },
            _ => DStmt::Exit,
        },
        _ => DStmt::Exit,
    }
}

/// A range-for that translates gives the loop of spec_range_dstmt.
#[verifier::rlimit(60)]
pub proof fn lemma_range_shape(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        spec_stmt(s, all, env, ps, sd).unwrap() == spec_range_dstmt(s, all, env, ps, sd),
{
}

/// A range-for gives one Dafny statement for the loop, the start of its index, its step and its element, and those of its body.
pub proof fn lemma_range_kept(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        count_dstmts(spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).unwrap()) == count_stmts(*s->RangeFor_5),
    ensures
        count_dstmt(spec_range_dstmt(s, all, env, ps, sd)) == count_stmt(s),
{
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                let first = DStmt::Local(x, spec_value_ty(xt, l, sd).unwrap(), spec_code(spec_range_elem(i, v, sc, ext), l).unwrap());
                let b: DStmts = List::Cons((Box::new(first), l), Box::new(db));
                assert(count_dstmt(first) == 1);
                assert(count_dstmts(b) == count_dstmt(first) + count_dstmts(db));
                assert(count_dstmt(DStmt::Local(i, DTy::UInt64, spec_range_zero())) == 1);
                assert(count_dstmt(spec_step(i, DTy::UInt64, true, false)) == 1);
                assert(count_stmt(s) == 4 + count_stmts(*body));
            },
            _ => {},
        },
        _ => {},
    }
}

/// The calls of a range-for are those of its body.
pub proof fn lemma_range_resolves(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        calls_resolve(spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).unwrap(), all, sd),
    ensures
        calls_resolve_stmt(spec_range_dstmt(s, all, env, ps, sd), all, sd),
{
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                let first = DStmt::Local(x, spec_value_ty(xt, l, sd).unwrap(), spec_code(spec_range_elem(i, v, sc, ext), l).unwrap());
                let b: DStmts = List::Cons((Box::new(first), l), Box::new(db));
                assert(calls_resolve_stmt(first, all, sd));
                assert(calls_resolve(b, all, sd));
                assert(calls_resolve_stmt(DStmt::Local(i, DTy::UInt64, spec_range_zero()), all, sd));
                assert(calls_resolve_stmt(spec_step(i, DTy::UInt64, true, false), all, sd));
            },
            _ => {},
        },
        _ => {},
    }
}

#[verifier::rlimit(30)]
pub proof fn lemma_stmt_kept(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == count_stmt(s),
    decreases s, 0nat,
{
    match s {
        Stmt::Return(_, _) => lemma_kept_return(s, all, env, ps, sd),
        Stmt::Block(b, _) => lemma_statements_kept(*b, all, env, ps, sd),
        Stmt::Local(_, _, _, _) => lemma_kept_local(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_kept_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetOwnField(_, _, _, _) => lemma_kept_set_own_field(s, all, env, ps, sd),
        Stmt::PushBack(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetFieldAt(_, _, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::PushField(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetThroughField(_, _, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::PopField(_, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::Switch(e, k, cs, l) => {
            lemma_cases_kept(*cs, all, env, ps, sd);
            let ce = spec_lift(e, all, l, sd, 0, true).unwrap();
            lemma_pre_count(ce.0, DStmt::Match(ce.1, k, Box::new(spec_cases(*cs, all, env, ps, sd).unwrap())));
        },
        Stmt::Call(_, _, _, _) => lemma_kept_call(s, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            lemma_statements_kept(*t, all, env, ps, sd);
            lemma_statements_kept(*f, all, env, ps, sd);
            let cc = spec_lift(c, all, l, sd, 0, true).unwrap();
            let body = DStmt::If(cc.1, Box::new(spec_stmts(*t, all, env, ps, sd).unwrap()), Box::new(spec_stmts(*f, all, env, ps, sd).unwrap()));
            lemma_pre_count(cc.0, body);
        },
        Stmt::While(_, _, body, _) => {
            lemma_statements_kept(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_kept(*init, all, env, ps, sd);
            lemma_stmt_kept(*step, all, spec_scope(*init, env), ps, sd);
            lemma_statements_kept(*body, all, spec_scope(*init, env), ps, sd);
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => {
            lemma_range_body_ok(s, all, env, ps, sd);
            lemma_range_shape(s, all, env, ps, sd);
            lemma_statements_kept(*body, all, spec_range_turn(s, env), ps, sd);
            lemma_range_kept(s, all, env, ps, sd);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches and loops included.
pub proof fn lemma_cases_kept(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_cases(cs, all, env, ps, sd).is_ok(),
    ensures
        count_dcases(spec_cases(cs, all, env, ps, sd).unwrap()) == count_cases(cs),
    decreases cs, 0nat,
{
    match cs {
        List::Cons((_, body), rest) => {
            lemma_statements_kept(*body, all, env, ps, sd);
            lemma_cases_kept(*rest, all, env, ps, sd);
        },
        List::Nil => {},
    }
}

pub proof fn lemma_statements_kept(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts(ss, all, env, ps, sd).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, all, env, ps, sd).unwrap()) == count_stmts(ss),
    decreases ss, 1nat,
{
    lemma_statements_kept_seq(ss, all, env, ps, sd);
    // The destructors at the end of a block are no statement of C++, decision 0178.
    lemma_block_end_dtors(ss, all, ps, sd);
    lemma_with_end_count(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), spec_block_end(ss, all, ps, sd), spec_last_place(ss));
}

pub proof fn lemma_statements_kept_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts_seq(ss, all, env, ps, sd).is_ok(),
    ensures
        count_dstmts(spec_stmts_seq(ss, all, env, ps, sd).unwrap()) == count_stmts(ss),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            lemma_stmt_kept(*s, all, env, ps, sd);
            lemma_statements_kept_seq(*rest, all, spec_scope(*s, env), ps, sd);
        },
        List::Nil => {},
    }
}

/// The count of two lists of statements is the sum of their counts.
pub proof fn lemma_count_append(a: DStmts, b: DStmts)
    ensures
        count_dstmts(spec_append(a, b)) == count_dstmts(a) + count_dstmts(b),
    decreases a,
{
    match a {
        List::Nil => {},
        List::Cons(_, rest) => lemma_count_append(*rest, b),
    }
}

/// The models hold a method, full or bare, with this key.
pub open spec fn has_method(ms: Models, key: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons(m, rest) => match m {
            Model::Full(method) => method.name == key || has_method(*rest, key),
            Model::Bare(name, _, _, _) => name == key || has_method(*rest, key),
            Model::Refused(_) => has_method(*rest, key),
        },
    }
}

/// Each call of the statements names a key of `all` that has a method.
pub open spec fn calls_resolve_cases(cs: DCases, all: Fns, sd: Structs) -> bool
    decreases cs,
{
    match cs {
        List::Nil => true,
        List::Cons((_, body), rest) => calls_resolve(*body, all, sd) && calls_resolve_cases(*rest, all, sd),
    }
}

pub open spec fn calls_resolve(ss: DStmts, all: Fns, sd: Structs) -> bool
    decreases ss,
{
    match ss {
        List::Nil => true,
        List::Cons((s, _), rest) => calls_resolve_stmt(*s, all, sd) && calls_resolve(*rest, all, sd),
    }
}

pub open spec fn calls_resolve_stmt(s: DStmt, all: Fns, sd: Structs) -> bool
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => calls_resolve(*t, all, sd) && calls_resolve(*f, all, sd),
        DStmt::Match(_, _, cs) => calls_resolve_cases(*cs, all, sd),
        DStmt::LocalCall(_, _, k, _) => spec_callable(all, k, sd),
        DStmt::ReturnCall(k, _) => spec_callable(all, k, sd),
        DStmt::ReturnUpdate(_, k, _) => spec_callable(all, k, sd),
        DStmt::AssignCall(_, k, _) => spec_callable(all, k, sd),
        DStmt::Update(_, k, _) => spec_callable(all, k, sd),
        DStmt::UpdateAt(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::LocalUpdate(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::CallStmt(k, _) => spec_callable(all, k, sd),
        DStmt::Pre(c, s) => calls_resolve_calls(c, all, sd) && calls_resolve_stmt(*s, all, sd),
        DStmt::Moved(s, _) => calls_resolve_stmt(*s, all, sd),
        DStmt::Gone(s, _, _) => calls_resolve_stmt(*s, all, sd),
        DStmt::Block(b) => calls_resolve(*b, all, sd),
        DStmt::Scope(b) => calls_resolve(*b, all, sd),
        DStmt::Dtors(b) => calls_resolve(*b, all, sd),
        DStmt::While(_, _, _, body) => calls_resolve(*body, all, sd),
        DStmt::For(init, _, _, _, _, body, step, _) => calls_resolve_stmt(*init, all, sd) && calls_resolve(*body, all, sd) && calls_resolve_stmt(*step, all, sd),
        _ => true,
    }
}

/// Each call that runs before a statement names a key of `all` that has a method.
pub open spec fn calls_resolve_calls(c: DCalls, all: Fns, sd: Structs) -> bool
    decreases c,
{
    match c {
        List::Nil => true,
        List::Cons(p, rest) => (match p {
            DPre::Call(_, _, k, _) => spec_callable(all, k, sd),
            DPre::Update(_, _, _, k, _) => spec_callable(all, k, sd),
            DPre::Step(_, _, _, _, _, _) => true,
        }) && calls_resolve_calls(*rest, all, sd),
    }
}

pub proof fn lemma_append_resolves(a: DCalls, b: DCalls, all: Fns, sd: Structs)
    ensures
        calls_resolve_calls(spec_append(a, b), all, sd) == (calls_resolve_calls(a, all, sd) && calls_resolve_calls(b, all, sd)),
    decreases a,
{
    match a {
        List::Cons(_, rest) => lemma_append_resolves(*rest, b, all, sd),
        List::Nil => {},
    }
}

/// Each call that a lifted expression runs first names a key that has a method.
#[verifier::rlimit(60)]
pub proof fn lemma_lift_resolves(e: Expr, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        spec_lift(e, all, line, sd, n, open).is_ok(),
    ensures
        calls_resolve_calls(spec_lift(e, all, line, sd, n, open).unwrap().0, all, sd),
    decreases e,
{
    match e {
        Expr::Call(k, _, args, _) => {
            lemma_lift_args_resolves(*args, all, line, sd, n, open);
            let (ca, da, n1) = spec_lift_args(*args, all, line, sd, n, open).unwrap();
            assert(spec_callable(all, k, sd));
            if !(spec_inline(all, k, sd) && spec_callable(all, k, sd)) {
                let dt = spec_callee_ty(all, k, line, sd).unwrap();
                // A call that writes back runs as an update, decision 0177, and any other as a call. Each names a callable key.
                let p = if spec_callee_writes(all, k) {
                    DPre::Update(n1, dt, spec_free_callee_writebacks(all, k, *args, line).unwrap(), k, da)
                } else {
                    DPre::Call(n1, dt, k, da)
                };
                assert(calls_resolve_calls(List::Nil, all, sd));
                assert(calls_resolve_calls(List::Cons(p, Box::new(List::Nil)), all, sd));
                lemma_append_resolves(ca, List::Cons(p, Box::new(List::Nil)), all, sd);
            }
        },
        Expr::Step(_, _, _, _) => {
            assert(calls_resolve_calls(List::Nil, all, sd));
        },
        Expr::Bin(op, a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let (ca, _, n1) = spec_lift(*a, all, line, sd, n, open).unwrap();
            let ob = open && !(op == BinOp::And || op == BinOp::Or);
            lemma_lift_resolves(*b, all, line, sd, n1, ob);
            lemma_append_resolves(ca, spec_lift(*b, all, line, sd, n1, ob).unwrap().0, all, sd);
        },
        Expr::Divide(_, a, b, _) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Shr(a, b, _) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Bits(_, a, b, _) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Index(a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Subspan(a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Not(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Neg(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Cast(_, a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Paren(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Brace(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Size(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Back(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Copy(a, _, _) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Field(a, _) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::HasValue(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Value(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Wrap(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Empty(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Construct(_, args) => lemma_lift_args_resolves(*args, all, line, sd, n, open),
        Expr::Cond(c, a, b) => {
            lemma_lift_resolves(*c, all, line, sd, n, open);
            let (cc, _, n1) = spec_lift(*c, all, line, sd, n, open).unwrap();
            lemma_lift_resolves(*a, all, line, sd, n1, false);
            let (ca, _, n2) = spec_lift(*a, all, line, sd, n1, false).unwrap();
            lemma_lift_resolves(*b, all, line, sd, n2, false);
            let cb = spec_lift(*b, all, line, sd, n2, false).unwrap().0;
            lemma_append_resolves(ca, cb, all, sd);
            lemma_append_resolves(cc, spec_append(ca, cb), all, sd);
        },
        _ => {},
    }
}

pub proof fn lemma_lift_args_resolves(args: Args, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        spec_lift_args(args, all, line, sd, n, open).is_ok(),
    ensures
        calls_resolve_calls(spec_lift_args(args, all, line, sd, n, open).unwrap().0, all, sd),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_args_resolves(*rest, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift_args(*rest, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        List::Nil => {},
    }
}

/// An expression that holds a node with no rule is refused.
pub proof fn lemma_unknown_lift_is_refused(e: Expr, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        unknown_expr(e),
    ensures
        spec_lift(e, all, line, sd, n, open).is_err(),
    decreases e,
{
    match e {
        Expr::Call(_, _, args, _) => lemma_unknown_lift_args_is_refused(*args, all, line, sd, n, open),
        Expr::Bin(op, a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open && !(op == BinOp::And || op == BinOp::Or));
            }
        },
        Expr::Divide(_, a, b, _) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Shr(a, b, _) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Bits(_, a, b, _) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        // The sequence of a count is a variable, so a node with no rule is in the test, which lifts with no call.
        Expr::CountIf(a, _, _, t) => {
            if unknown_expr(*t) {
                lemma_unknown_lift_is_refused(*t, List::Nil, line, List::Nil, 0, false);
            } else {
                assert(!(*a is Var)) by {
                    if *a is Var {
                        assert(!unknown_expr(*a));
                    }
                }
            }
        },
        Expr::Index(a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Subspan(a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Not(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Neg(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Cast(_, a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Paren(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Brace(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Size(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Back(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Copy(a, _, _) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Field(a, _) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::HasValue(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Value(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Wrap(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Empty(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Construct(_, args) => lemma_unknown_lift_args_is_refused(*args, all, line, sd, n, open),
        Expr::Cond(c, a, b) => {
            if unknown_expr(*c) {
                lemma_unknown_lift_is_refused(*c, all, line, sd, n, open);
            } else if spec_lift(*c, all, line, sd, n, open).is_ok() {
                {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false);
            } else if spec_lift(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false).unwrap().2, false);
            }
        }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_lift_args_is_refused(args: Args, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        unknown_args(args),
    ensures
        spec_lift_args(args, all, line, sd, n, open).is_err(),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_args_is_refused(*rest, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        List::Nil => {},
    }
}

/// A lift where a call has no place runs no call, so a loop condition drops none.
pub proof fn lemma_closed_runs_no_call(e: Expr, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lift(e, all, line, sd, n, false).is_ok(),
    ensures
        spec_lift(e, all, line, sd, n, false).unwrap().0 == List::Nil,
    decreases e,
{
    match e {
        Expr::Bin(_, a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Divide(_, a, b, _) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Shr(a, b, _) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Bits(_, a, b, _) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Index(a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Subspan(a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Not(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Neg(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Cast(_, a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Paren(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Brace(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Size(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Back(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Copy(a, _, _) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Field(a, _) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::HasValue(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Value(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Wrap(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Empty(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Construct(_, args) => lemma_closed_args_run_no_call(*args, all, line, sd, n),
        // A call of a const virtual function is its function in place, and its arguments run no call, decision 0172.
        Expr::Call(_, _, args, _) => lemma_closed_args_run_no_call(*args, all, line, sd, n),
        Expr::Cond(c, a, b) => {
            lemma_closed_runs_no_call(*c, all, line, sd, n);
            let n1 = spec_lift(*c, all, line, sd, n, false).unwrap().2;
            lemma_closed_runs_no_call(*a, all, line, sd, n1);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n1, false).unwrap().2);
        },
        _ => {},
    }
}

pub proof fn lemma_closed_args_run_no_call(args: Args, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lift_args(args, all, line, sd, n, false).is_ok(),
    ensures
        spec_lift_args(args, all, line, sd, n, false).unwrap().0 == List::Nil,
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_args_run_no_call(*rest, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        List::Nil => {},
    }
}

/// The calls before a statement resolve when each of them names a key with a method.
pub proof fn lemma_pre_resolves(c: DCalls, s: DStmt, all: Fns, sd: Structs)
    ensures
        calls_resolve_stmt(spec_pre(c, s), all, sd) == (calls_resolve_calls(c, all, sd) && calls_resolve_stmt(s, all, sd)),
{
}

/// A call that stands alone names a key with a method, and so does each call in its arguments.
pub proof fn lemma_call_lift_resolves(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs)
    requires
        spec_call_lift(key, name, args, at, all, line, sd).is_ok(),
    ensures
        spec_callable(all, key, sd),
        calls_resolve_calls(spec_call_lift(key, name, args, at, all, line, sd).unwrap().0, all, sd),
{
    lemma_lift_args_resolves(args, all, line, sd, 0, true);
}

/// The value of a return or of a write resolves its calls.
pub proof fn lemma_value_resolves(e: Expr, all: Fns, line: u32, sd: Structs)
    ensures
        (e is Call && spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_ok()) ==> spec_callable(all, e->Call_0, sd)
            && calls_resolve_calls(spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).unwrap().0, all, sd),
        (!(e is Call) && spec_lift(e, all, line, sd, 0, true).is_ok()) ==> calls_resolve_calls(spec_lift(e, all, line, sd, 0, true).unwrap().0, all, sd),
{
    if e is Call {
        if spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_ok() {
            lemma_call_lift_resolves(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd);
        }
    } else if spec_lift(e, all, line, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, line, sd, 0, true);
    }
}

/// A `return`: the value, and with live locals the destructors, decision 0178.
pub proof fn lemma_resolves_return(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Return,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_return_stmt);
    let e = spec_unmove(s->Return_0).0;
    let l = s->Return_1;
    if !(spec_live(env, sd) is Nil) {
        lemma_resolves_dying_return(e, l, all, env, ps, sd);
    } else {
        lemma_resolves_value_return(e, l, all, ps, sd);
    }
}

/// A `return` with no live local.
pub proof fn lemma_resolves_value_return(e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_return(e, l, all, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_return(e, l, all, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    if e is List {
        lemma_lift_args_resolves(*e->List_0, all, l, sd, 0, true);
        let (c, da, _) = spec_lift_args(*e->List_0, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::Return(DExpr::SeqLit(Box::new(da))), all, sd);
    } else if e is Construct {
        lemma_lift_args_resolves(*e->Construct_1, all, l, sd, 0, true);
        let (c, da, _) = spec_lift_args(*e->Construct_1, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::Return(DExpr::Ctor(e->Construct_0, Box::new(da))), all, sd);
    } else if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_lower_resolves(e, None, false, all, l, sd, 0);
    } else {
        lemma_value_resolves(e, all, l, sd);
    }
}

/// The end of a block that the destructors leave: each destructor, then the exit. Each destructor names a method.
pub proof fn lemma_resolves_dtors_exit(ds: DStmts, l: u32, all: Fns, sd: Structs)
    requires
        calls_resolve(ds, all, sd),
    ensures
        calls_resolve(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))), all, sd),
{
    reveal_with_fuel(calls_resolve, 3);
    let ex: DStmts = List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil));
    assert(calls_resolve(ex, all, sd));
    assert(calls_resolve_stmt(DStmt::Dtors(Box::new(ds)), all, sd));
}

/// A `return` with live locals: the value lifts or lowers, then the destructors run, decision 0178.
pub proof fn lemma_resolves_dying_return(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_dying_return(e, l, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_dying_return(e, l, all, env, ps, sd).unwrap(), all, sd),
{
    lemma_dtor_calls_resolve(spec_live(env, sd), all, ps, sd, l);
    let ds = spec_dtor_calls(spec_live(env, sd), all, ps, sd, l).unwrap();
    lemma_resolves_dtors_exit(ds, l, all, sd);
    let tail: DStmts = List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))));
    if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_lower_resolves(e, None, true, all, l, sd, 0);
        let (ss, _) = spec_lower(e, None, true, all, l, sd, 0).unwrap();
        lemma_resolve_append(ss, tail, all, sd);
    } else {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetResult(d), all, sd);
        let b: DStmts = List::Cons((Box::new(spec_pre(c, DStmt::SetResult(d))), l), Box::new(tail));
        assert(calls_resolve(b, all, sd));
    }
}

pub proof fn lemma_resolves_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_assign_stmt);
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->Assign_1;
    let l = s->Assign_2;
    if spec_is_mut(ps, s->Assign_0) {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOut(s->Assign_0, d), all, sd);
    } else {
        lemma_value_resolves(e, all, l, sd);
    }
}

pub proof fn lemma_resolves_set_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->SetField_1;
    let l = s->SetField_2;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetField(s->SetField_0, d), all, sd);
    }
}

/// A push_back runs the calls of its value before it, decision 0170, and each names a method.
pub proof fn lemma_resolves_push(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is PushBack,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let v = s->PushBack_0;
    let e = s->PushBack_1;
    let l = s->PushBack_2;
    if e is Wrap && spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(d))), all, sd);
        lemma_pre_resolves(c, DStmt::Assign(v, DExpr::Append(Box::new(DExpr::Var(v)), Box::new(d))), all, sd);
    }
}

pub proof fn lemma_resolves_set_ref_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetRefField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->SetRefField_2;
    let l = s->SetRefField_3;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOutField(s->SetRefField_0, s->SetRefField_1, d), all, sd);
    }
}

pub proof fn lemma_resolves_set_own_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetOwnField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 3);
    let e = spec_unmove(s->SetOwnField_2).0;
    let l = s->SetOwnField_3;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOwnField(s->SetOwnField_0, s->SetOwnField_1, d), all, sd);
        let inner = spec_pre(c, DStmt::SetOwnField(s->SetOwnField_0, s->SetOwnField_1, d));
        assert(calls_resolve_stmt(inner, all, sd));
        lemma_moved_resolves(inner, spec_unmove(s->SetOwnField_2).1, spec_vec_moves(s->SetOwnField_2), all, sd);
    }
}

/// A statement that holds no call gives a Dafny statement that holds none.
#[verifier::rlimit(60)]
pub proof fn lemma_resolves_plain(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Step || s is Assert || s is Apply || s is Unknown || s is SetIndex || s is SetFieldAt || s is PushField || s is PopField || s is SetThroughField
            || s is Sort
            || s is SortBy,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
}

/// An exit with live locals runs each destructor first, decision 0178. Each destructor names a method.
pub proof fn lemma_resolves_exit(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Exit,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    if !(spec_live(env, sd) is Nil) {
        let l = s->Exit_0;
        lemma_dtor_calls_resolve(spec_live(env, sd), all, ps, sd, l);
        lemma_resolves_dtors_exit(spec_dtor_calls(spec_live(env, sd), all, ps, sd, l).unwrap(), l, all, sd);
        assert(spec_stmt(s, all, env, ps, sd) == spec_dying_exit(l, all, env, ps, sd));
    }
}

#[verifier::rlimit(30)]
pub proof fn lemma_resolves_local(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Local,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_local_stmt);
    reveal_with_fuel(calls_resolve_stmt, 3);
    let l = s->Local_3;
    // The vector arm reads the start value as it is, and the other arm with its moves taken out, decision 0171.
    let e1 = s->Local_2;
    let e2 = spec_unmove(s->Local_2).0;
    // `k` copies of a value start an array of length `k`, and the value lifts alone, decision 0196.
    if let Expr::Fill(_, x) = e1 {
        if spec_lift(*x, all, l, sd, 0, true).is_ok() {
            lemma_lift_resolves(*x, all, l, sd, 0, true);
        }
    }
    // `v(n, x)` lifts its count, then its value, decision 0185.
    if let Expr::Fill(c, x) = e1 {
        if spec_lift(*c, all, l, sd, 0, true).is_ok() {
            lemma_lift_resolves(*c, all, l, sd, 0, true);
            let (c1, _, n1) = spec_lift(*c, all, l, sd, 0, true).unwrap();
            if spec_lift(*x, all, l, sd, n1, true).is_ok() {
                lemma_lift_resolves(*x, all, l, sd, n1, true);
                lemma_append_resolves(c1, spec_lift(*x, all, l, sd, n1, true).unwrap().0, all, sd);
            }
        }
    }
    // A local std::array from a brace list lifts each value, decision 0184.
    if let Expr::List(args) = e1 {
        if spec_lift_args(*args, all, l, sd, 0, true).is_ok() {
            lemma_lift_args_resolves(*args, all, l, sd, 0, true);
        }
    }
    lemma_value_resolves(e1, all, l, sd);
    lemma_value_resolves(e2, all, l, sd);
    if let Expr::Call(k, nm, args, at) = e1 {
        if let List::Cons(_, rest) = *args {
            if spec_call_lift(k, nm, *rest, at, all, l, sd).is_ok() {
                lemma_call_lift_resolves(k, nm, *rest, at, all, l, sd);
            }
        }
    }
    if let Expr::Call(k, nm, args, at) = e2 {
        if let List::Cons(_, rest) = *args {
            if spec_call_lift(k, nm, *rest, at, all, l, sd).is_ok() {
                lemma_call_lift_resolves(k, nm, *rest, at, all, l, sd);
            }
        }
    }
    // The other arm moves after its value, decisions 0171 and 0194.
    if spec_value_ty(s->Local_1, l, sd).is_ok() {
        let dt = spec_value_ty(s->Local_1, l, sd).unwrap();
        if spec_local_value(s->Local_0, dt, e2, l, all, ps, sd).is_ok() {
            let inner = spec_local_value(s->Local_0, dt, e2, l, all, ps, sd).unwrap();
            assert(calls_resolve_stmt(inner, all, sd));
            lemma_moved_resolves(inner, spec_unmove(e1).1, spec_vec_moves(e1), all, sd);
        }
    }
}

pub proof fn lemma_resolves_call(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Call,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 3);
    let k = s->Call_0;
    let nm = s->Call_1;
    let args = spec_unmove_args(*s->Call_2).0;
    let l = s->Call_3;
    if spec_call_lift(k, nm, args, l, all, l, sd).is_ok() {
        lemma_call_lift_resolves(k, nm, args, l, all, l, sd);
    }
    if let List::Cons(_, rest) = args {
        if spec_call_lift(k, nm, *rest, l, all, l, sd).is_ok() {
            lemma_call_lift_resolves(k, nm, *rest, l, all, l, sd);
        }
    }
    if spec_call_stmt(k, nm, args, l, all, ps, sd).is_ok() {
        let inner = spec_call_stmt(k, nm, args, l, all, ps, sd).unwrap();
        assert(calls_resolve_stmt(inner, all, sd));
        lemma_moved_resolves(inner, spec_unmove_args(*s->Call_2).1, spec_vec_moves_args(*s->Call_2), all, sd);
    }
}

#[verifier::rlimit(60)]
pub proof fn lemma_stmt_calls_resolve(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
    decreases s, 0nat,
{
    match s {
        Stmt::Return(_, _) => lemma_resolves_return(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_resolves_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_resolves_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_resolves_set_ref_field(s, all, env, ps, sd),
        Stmt::SetOwnField(_, _, _, _) => lemma_resolves_set_own_field(s, all, env, ps, sd),
        Stmt::Switch(e, k, cs, l) => {
            lemma_cases_calls_resolve(*cs, all, env, ps, sd);
            lemma_lift_resolves(e, all, l, sd, 0, true);
            let (ce, de, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
            lemma_pre_resolves(ce, DStmt::Match(de, k, Box::new(spec_cases(*cs, all, env, ps, sd).unwrap())), all, sd);
        },
        Stmt::Local(_, _, _, _) => lemma_resolves_local(s, all, env, ps, sd),
        Stmt::Call(_, _, _, _) => lemma_resolves_call(s, all, env, ps, sd),
        Stmt::Step(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Exit(_) => lemma_resolves_exit(s, all, env, ps, sd),
        Stmt::Block(b, _) => lemma_stmts_calls_resolve(*b, all, env, ps, sd),
        Stmt::Assert(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Apply(_, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Unknown(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetIndex(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetFieldAt(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::PushField(_, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetThroughField(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::PopField(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::PushBack(_, _, _) => lemma_resolves_push(s, all, env, ps, sd),
        Stmt::Sort(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SortBy(_, _, _, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            lemma_stmts_calls_resolve(*t, all, env, ps, sd);
            lemma_stmts_calls_resolve(*f, all, env, ps, sd);
            lemma_lift_resolves(c, all, l, sd, 0, true);
            let (cc, dc, _) = spec_lift(c, all, l, sd, 0, true).unwrap();
            let body = DStmt::If(dc, Box::new(spec_stmts(*t, all, env, ps, sd).unwrap()), Box::new(spec_stmts(*f, all, env, ps, sd).unwrap()));
            lemma_pre_resolves(cc, body, all, sd);
        },
        Stmt::While(_, _, body, _) => {
            lemma_stmts_calls_resolve(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_calls_resolve(*init, all, env, ps, sd);
            lemma_stmt_calls_resolve(*step, all, spec_scope(*init, env), ps, sd);
            lemma_stmts_calls_resolve(*body, all, spec_scope(*init, env), ps, sd);
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => {
            lemma_range_body_ok(s, all, env, ps, sd);
            lemma_range_shape(s, all, env, ps, sd);
            lemma_stmts_calls_resolve(*body, all, spec_range_turn(s, env), ps, sd);
            lemma_range_resolves(s, all, env, ps, sd);
        },
    }
}

pub proof fn lemma_cases_calls_resolve(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_cases(cs, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_cases(spec_cases(cs, all, env, ps, sd).unwrap(), all, sd),
    decreases cs, 0nat,
{
    match cs {
        List::Cons((_, body), rest) => {
            lemma_stmts_calls_resolve(*body, all, env, ps, sd);
            lemma_cases_calls_resolve(*rest, all, env, ps, sd);
        },
        List::Nil => {},
    }
}

pub proof fn lemma_stmts_calls_resolve(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts(ss, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve(spec_stmts(ss, all, env, ps, sd).unwrap(), all, sd),
    decreases ss, 1nat,
{
    lemma_stmts_calls_resolve_seq(ss, all, env, ps, sd);
    lemma_block_end_resolves(ss, all, ps, sd);
    lemma_with_end_resolves(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), spec_block_end(ss, all, ps, sd), spec_last_place(ss), all, sd);
}

pub proof fn lemma_stmts_calls_resolve_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts_seq(ss, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), all, sd),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all, env, ps, sd);
            lemma_stmts_calls_resolve_seq(*rest, all, spec_scope(*s, env), ps, sd);
        },
        List::Nil => {},
    }
}

/// A key with a signature in the subset has a method among the models of the file.
pub proof fn lemma_callable_has_method(fs: Fns, all: Fns, key: u32, sd: Structs)
    requires
        spec_callable(fs, key, sd),
    ensures
        has_method(spec_unit(fs, all, sd), key),
    decreases fs,
{
    match fs {
        List::Cons(f, rest) => {
            if !(f.name == key && has_signature(*f, sd)) {
                lemma_callable_has_method(*rest, all, key, sd);
            }
        },
        List::Nil => {},
    }
}

/// The locals of the moved parameters hold no call, so the block of them resolves when the body does, decision 0186.
pub proof fn lemma_param_locals_resolve(mp: List<(u32, DTy)>, line: u32, tail: DStmts, all: Fns, sd: Structs)
    requires
        calls_resolve(tail, all, sd),
    ensures
        calls_resolve(spec_param_locals(mp, line, tail), all, sd),
    decreases mp,
{
    match mp {
        List::Nil => {},
        List::Cons((n, dt), rest) => {
            lemma_param_locals_resolve(*rest, line, tail, all, sd);
            assert(calls_resolve_stmt(DStmt::Local(n, dt, DExpr::Var(n)), all, sd));
        },
    }
}

pub proof fn lemma_param_block_resolves(mp: List<(u32, DTy)>, line: u32, body: DStmts, all: Fns, sd: Structs)
    requires
        calls_resolve(body, all, sd),
    ensures
        calls_resolve(spec_param_block(mp, line, body), all, sd),
{
    lemma_param_locals_resolve(mp, line, body, all, sd);
    reveal_with_fuel(calls_resolve, 2);
    reveal_with_fuel(calls_resolve_stmt, 2);
}

/// Each call in a full method of the file names a method of the model of the file, so the Dafny file resolves.
pub proof fn lemma_calls_resolve(f: Function, all: Fns, sd: Structs)
    requires
        spec_function(f, all, sd) is Full,
    ensures
        calls_resolve(spec_function(f, all, sd)->Full_0.body, all, sd),
        forall|k: u32| spec_callable(all, k, sd) ==> #[trigger] has_method(spec_unit(all, all, sd), k),
{
    if !f.trusted {
        let ms = spec_moves_stmts(f.body);
        lemma_stmts_calls_resolve(f.body, all, f.params, spec_kept_params(f.params, ms), sd);
        lemma_param_block_resolves(spec_moved_params(f.params, ms), f.line, spec_stmts(f.body, all, f.params, spec_kept_params(f.params, ms), sd).unwrap(), all, sd);
    }
    assert forall|k: u32| spec_callable(all, k, sd) implies #[trigger] has_method(spec_unit(all, all, sd), k) by {
        lemma_callable_has_method(all, all, k, sd);
    }
}

} // verus!

//! The translator: a write inside an expression, decision 0177. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ a write inside an expression, decision 0177

/// A step before a statement that writes: an update or a step of a name.
pub open spec fn spec_pre_writes(p: DPre) -> bool {
    p is Update || p is Step
}

pub fn pre_writes(p: &DPre) -> (r: bool)
    ensures
        r == spec_pre_writes(*p),
{
    matches!(p, DPre::Update(..) | DPre::Step(..))
}

/// The count of the steps that write.
pub open spec fn spec_count_writes(c: DCalls) -> nat
    decreases c,
{
    match c {
        List::Nil => 0,
        List::Cons(p, rest) => (if spec_pre_writes(p) { 1nat } else { 0nat }) + spec_count_writes(*rest),
    }
}

/// More than one step writes.
pub open spec fn spec_writes_twice(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => if spec_pre_writes(p) {
            spec_any_write(*rest)
        } else {
            spec_writes_twice(*rest)
        },
    }
}

pub open spec fn spec_any_write(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => spec_pre_writes(p) || spec_any_write(*rest),
    }
}

pub fn writes_twice(c: &DCalls) -> (r: bool)
    ensures
        r == spec_writes_twice(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => if pre_writes(p) {
            any_write(rest)
        } else {
            writes_twice(rest)
        },
    }
}

pub fn any_write(c: &DCalls) -> (r: bool)
    ensures
        r == spec_any_write(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => pre_writes(p) || any_write(rest),
    }
}

/// Any step that writes a name with `x++`.
pub open spec fn spec_any_step(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => p is Step || spec_any_step(*rest),
    }
}

pub fn any_step(c: &DCalls) -> (r: bool)
    ensures
        r == spec_any_step(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => matches!(p, DPre::Step(..)) || any_step(rest),
    }
}

/// The names of the places that the steps write.
pub open spec fn spec_obj_names(os: Objs) -> Names
    decreases os,
{
    match os {
        List::Nil => List::Nil,
        List::Cons(o, rest) => match o {
            Obj::Local(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Out(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Owned(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Down(v, _, _) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Object => spec_obj_names(*rest),
            Obj::Field(_) => spec_obj_names(*rest),
        },
    }
}

pub fn obj_names(os: &Objs) -> (r: Names)
    ensures
        r == spec_obj_names(*os),
    decreases os,
{
    match os {
        List::Nil => List::Nil,
        List::Cons(o, rest) => match o {
            Obj::Local(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Out(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Owned(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Down(v, _, _) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Object => obj_names(rest),
            Obj::Field(_) => obj_names(rest),
        },
    }
}

pub open spec fn spec_written_names(c: DCalls) -> Names
    decreases c,
{
    match c {
        List::Nil => List::Nil,
        List::Cons(p, rest) => match p {
            DPre::Update(_, _, os, _, _) => spec_append(spec_obj_names(os), spec_written_names(*rest)),
            DPre::Step(_, _, v, _, _, _) => List::Cons(v, Box::new(spec_written_names(*rest))),
            DPre::Call(_, _, _, _) => spec_written_names(*rest),
        },
    }
}

pub fn written_names(c: &DCalls) -> (r: Names)
    ensures
        r == spec_written_names(*c),
    decreases c,
{
    match c {
        List::Nil => List::Nil,
        List::Cons(p, rest) => match p {
            DPre::Update(_, _, os, _, _) => append(obj_names(os), written_names(rest)),
            DPre::Step(_, _, v, _, _, _) => List::Cons(*v, Box::new(written_names(rest))),
            DPre::Call(_, _, _, _) => written_names(rest),
        },
    }
}

/// The name stands at least twice in the list.
pub open spec fn spec_has_twice(l: Names, x: u32) -> bool
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(h, t) => if h == x {
            spec_has(*t, x)
        } else {
            spec_has_twice(*t, x)
        },
    }
}

pub fn has_twice(l: &Names, x: u32) -> (r: bool)
    ensures
        r == spec_has_twice(*l, x),
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(h, t) => if *h == x {
            has(t, x)
        } else {
            has_twice(t, x)
        },
    }
}

/// The first written name that the region also reads elsewhere.
pub open spec fn spec_read_too(ws: Names, reads: Names, line: u32) -> Option<Refusal>
    decreases ws,
{
    match ws {
        List::Nil => None,
        List::Cons(x, rest) => if spec_has_twice(reads, x) {
            Some(Refusal::WriteRead(x, line))
        } else {
            spec_read_too(*rest, reads, line)
        },
    }
}

pub fn read_too(ws: &Names, reads: &Names, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_read_too(*ws, *reads, line),
    decreases ws,
{
    match ws {
        List::Nil => None,
        List::Cons(x, rest) => if has_twice(reads, *x) {
            Some(Refusal::WriteRead(*x, line))
        } else {
            read_too(rest, reads, line)
        },
    }
}

/// A place that a step writes and that the function cannot write: a reference parameter that is none, or a parameter by value.
pub open spec fn spec_bad_obj(o: Obj, ps: Params, line: u32) -> Option<Refusal> {
    match o {
        Obj::Out(v) => if spec_is_mut(ps, v) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Local(v) => if spec_get(ps, v) is Some { Some(Refusal::WriteParam(v, line)) } else { None },
        Obj::Object => if spec_writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Field(_) => if spec_writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Owned(v) => if spec_get(ps, v) is Some { Some(Refusal::NoTarget(line)) } else { None },
        Obj::Down(v, _, _) => if spec_get(ps, v) is Some { Some(Refusal::NoTarget(line)) } else { None },
    }
}

pub fn bad_obj(o: Obj, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_obj(o, *ps, line),
{
    match o {
        Obj::Out(v) => if is_mut(ps, v) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Local(v) => if get(ps, v).is_some() { Some(Refusal::WriteParam(v, line)) } else { None },
        Obj::Object => if writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Field(_) => if writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Owned(v) => if get(ps, v).is_some() { Some(Refusal::NoTarget(line)) } else { None },
        Obj::Down(v, _, _) => if get(ps, v).is_some() { Some(Refusal::NoTarget(line)) } else { None },
    }
}

pub open spec fn spec_bad_objs(os: Objs, ps: Params, line: u32) -> Option<Refusal>
    decreases os,
{
    match os {
        List::Nil => None,
        List::Cons(o, rest) => match spec_bad_obj(o, ps, line) {
            Some(r) => Some(r),
            None => spec_bad_objs(*rest, ps, line),
        },
    }
}

pub fn bad_objs(os: &Objs, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_objs(*os, *ps, line),
    decreases os,
{
    match os {
        List::Nil => None,
        List::Cons(o, rest) => match bad_obj(*o, ps, line) {
            Some(r) => Some(r),
            None => bad_objs(rest, ps, line),
        },
    }
}

/// The first step that writes a place the function cannot write. The steps read each place from the type of the argument alone,
/// `spec_free_target`, so the parameters decide here.
pub open spec fn spec_bad_pres(c: DCalls, ps: Params, line: u32) -> Option<Refusal>
    decreases c,
{
    match c {
        List::Nil => None,
        List::Cons(p, rest) => match (match p {
            DPre::Update(_, _, os, _, _) => spec_bad_objs(os, ps, line),
            DPre::Step(_, _, v, _, _, out) => spec_bad_obj(if out { Obj::Out(v) } else { Obj::Local(v) }, ps, line),
            DPre::Call(_, _, _, _) => None,
        }) {
            Some(r) => Some(r),
            None => spec_bad_pres(*rest, ps, line),
        },
    }
}

pub fn bad_pres(c: &DCalls, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_pres(*c, *ps, line),
    decreases c,
{
    match c {
        List::Nil => None,
        List::Cons(p, rest) => {
            let b = match p {
                DPre::Update(_, _, os, _, _) => bad_objs(os, ps, line),
                DPre::Step(_, _, v, _, _, out) => bad_obj(if *out { Obj::Out(*v) } else { Obj::Local(*v) }, ps, line),
                DPre::Call(_, _, _, _) => None,
            };
            match b {
                Some(r) => Some(r),
                None => bad_pres(rest, ps, line),
            }
        },
    }
}

/// The check of one region, where C++ fixes no order: each write goes to a place the function can write, at most one write
/// runs, and the name it writes is read nowhere else in the region. The region is lifted as the translation lifts it. A region
/// that does not lift has no check, because its translation refuses it.
pub open spec fn spec_check_region(e: Expr, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift(e, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match spec_bad_pres(c, ps, line) {
            Some(r) => Some(r),
            None => if spec_writes_twice(c) {
                Some(Refusal::TwoWrites(line))
            } else {
                spec_read_too(spec_written_names(c), spec_var_names(e), line)
            },
        },
    }
}

pub fn check_region(e: &Expr, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_region(*e, *all, *ps, *sd, line),
{
    match lift(e, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match bad_pres(&c, ps, line) {
            Some(r) => Some(r),
            None => if writes_twice(&c) {
                Some(Refusal::TwoWrites(line))
            } else {
                read_too(&written_names(&c), &var_names(e), line)
            },
        },
    }
}

/// The check of an expression: the sides of `&&` and `||`, and the condition and the branches of `?:`, are regions of their own,
/// because C++ runs them in order.
pub open spec fn spec_check_expr(e: Expr, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal>
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => if op == BinOp::And || op == BinOp::Or {
            match spec_check_expr(*a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => spec_check_expr(*b, all, ps, sd, line),
            }
        } else {
            spec_check_region(e, all, ps, sd, line)
        },
        Expr::Cond(c, a, b) => match spec_check_expr(*c, all, ps, sd, line) {
            Some(r) => Some(r),
            None => match spec_check_expr(*a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => spec_check_expr(*b, all, ps, sd, line),
            },
        },
        Expr::Paren(a) => spec_check_expr(*a, all, ps, sd, line),
        // The count and the value of `v(n, x)` are one region, as the arguments of a call are, decision 0185.
        Expr::Fill(c, x) => match spec_lift(*c, all, line, sd, 0, true) {
            Err(_) => None,
            Ok((c1, _, n1)) => match spec_lift(*x, all, line, sd, n1, true) {
                Err(_) => None,
                Ok((c2, _, _)) => spec_check_pres(spec_append(c1, c2), spec_var_names(e), ps, line),
            },
        },
        _ => spec_check_region(e, all, ps, sd, line),
    }
}

/// The checks of a region on the calls `c` that run before it, and the names `reads` that it reads, decision 0177.
pub open spec fn spec_check_pres(c: DCalls, reads: Names, ps: Params, line: u32) -> Option<Refusal> {
    match spec_bad_pres(c, ps, line) {
        Some(r) => Some(r),
        None => if spec_writes_twice(c) {
            Some(Refusal::TwoWrites(line))
        } else {
            spec_read_too(spec_written_names(c), reads, line)
        },
    }
}

pub fn check_pres(c: &DCalls, reads: &Names, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_pres(*c, *reads, *ps, line),
{
    match bad_pres(c, ps, line) {
        Some(r) => Some(r),
        None => if writes_twice(c) {
            Some(Refusal::TwoWrites(line))
        } else {
            read_too(&written_names(c), reads, line)
        },
    }
}

pub fn check_expr(e: &Expr, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_expr(*e, *all, *ps, *sd, line),
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => if *op == BinOp::And || *op == BinOp::Or {
            match check_expr(a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => check_expr(b, all, ps, sd, line),
            }
        } else {
            check_region(e, all, ps, sd, line)
        },
        Expr::Cond(c, a, b) => match check_expr(c, all, ps, sd, line) {
            Some(r) => Some(r),
            None => match check_expr(a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => check_expr(b, all, ps, sd, line),
            },
        },
        Expr::Paren(a) => check_expr(a, all, ps, sd, line),
        Expr::Fill(c, x) => match lift(c, all, line, sd, 0, true) {
            Err(_) => None,
            Ok((c1, _, n1)) => match lift(x, all, line, sd, n1, true) {
                Err(_) => None,
                Ok((c2, _, _)) => check_pres(&append(c1, c2), &var_names(e), ps, line),
            },
        },
        _ => check_region(e, all, ps, sd, line),
    }
}

/// A write in the condition of a loop, which runs at each turn, has no rule.
pub open spec fn spec_loop_write(c: Expr, all: Fns, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift(c, all, line, sd, 0, true) {
        Ok((cs, _, _)) => if spec_any_step(cs) { Some(Refusal::LoopWrite(line)) } else { None },
        Err(_) => None,
    }
}

pub fn loop_write(c: &Expr, all: &Fns, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_loop_write(*c, *all, *sd, line),
{
    match lift(c, all, line, sd, 0, true) {
        Ok((cs, _, _)) => if any_step(&cs) { Some(Refusal::LoopWrite(line)) } else { None },
        Err(_) => None,
    }
}

/// The check of the writes of a statement before it translates, decision 0177. A call that stands alone writes in its own body,
/// so only its arguments are a region. A statement with no expression of code has no check.
pub open spec fn spec_write_check(s: Stmt, all: Fns, ps: Params, sd: Structs) -> Option<Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::Local(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::Assign(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetField(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetRefField(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetOwnField(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::PushBack(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::If(c, _, _, l) => spec_check_expr(c, all, ps, sd, l),
        Stmt::Switch(e, _, _, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetIndex(_, i, e, l) => match spec_check_expr(i, all, ps, sd, l) {
            Some(r) => Some(r),
            None => spec_check_expr(e, all, ps, sd, l),
        },
        Stmt::SetFieldAt(_, i, e, l) => match spec_check_expr(i, all, ps, sd, l) {
            Some(r) => Some(r),
            None => spec_check_expr(e, all, ps, sd, l),
        },
        Stmt::PushField(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetThroughField(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::Call(_, _, args, l) => spec_check_args(*args, all, ps, sd, l),
        Stmt::While(c, _, _, l) => spec_loop_write(c, all, sd, l),
        Stmt::For(init, c, step, _, _, l) => match spec_write_check(*init, all, ps, sd) {
            Some(r) => Some(r),
            None => match spec_loop_write(c, all, sd, l) {
                Some(r) => Some(r),
                None => spec_write_check(*step, all, ps, sd),
            },
        },
        _ => None,
    }
}

/// The arguments of a call that stands alone, one region.
pub open spec fn spec_check_args(args: Args, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift_args(args, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match spec_bad_pres(c, ps, line) {
            Some(r) => Some(r),
            None => if spec_writes_twice(c) {
                Some(Refusal::TwoWrites(line))
            } else {
                spec_read_too(spec_written_names(c), spec_var_names_args(args), line)
            },
        },
    }
}

pub fn check_args(args: &Args, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_args(*args, *all, *ps, *sd, line),
{
    match lift_args(args, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match bad_pres(&c, ps, line) {
            Some(r) => Some(r),
            None => if writes_twice(&c) {
                Some(Refusal::TwoWrites(line))
            } else {
                read_too(&written_names(&c), &var_names_args(args), line)
            },
        },
    }
}

pub fn write_check(s: &Stmt, all: &Fns, ps: &Params, sd: &Structs) -> (r: Option<Refusal>)
    ensures
        r == spec_write_check(*s, *all, *ps, *sd),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::Local(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::Assign(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetField(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetRefField(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetOwnField(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::PushBack(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::If(c, _, _, l) => check_expr(c, all, ps, sd, *l),
        Stmt::Switch(e, _, _, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetIndex(_, i, e, l) => match check_expr(i, all, ps, sd, *l) {
            Some(r) => Some(r),
            None => check_expr(e, all, ps, sd, *l),
        },
        Stmt::SetFieldAt(_, i, e, l) => match check_expr(i, all, ps, sd, *l) {
            Some(r) => Some(r),
            None => check_expr(e, all, ps, sd, *l),
        },
        Stmt::PushField(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetThroughField(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::Call(_, _, args, l) => check_args(args, all, ps, sd, *l),
        Stmt::While(c, _, _, l) => loop_write(c, all, sd, *l),
        Stmt::For(init, c, step, _, _, l) => match write_check(init, all, ps, sd) {
            Some(r) => Some(r),
            None => match loop_write(c, all, sd, *l) {
                Some(r) => Some(r),
                None => write_check(step, all, ps, sd),
            },
        },
        _ => None,
    }
}

/// A part of an expression that runs a call or a write, or that the lift refuses as a call out of place.
pub open spec fn spec_needs_if(e: Expr, all: Fns, line: u32, sd: Structs) -> bool {
    match spec_lift(e, all, line, sd, 0, true) {
        Ok((c, _, _)) => !(c is Nil),
        Err(r) => r is Place,
    }
}

pub fn needs_if(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_needs_if(*e, *all, line, *sd),
{
    match lift(e, all, line, sd, 0, true) {
        Ok((c, _, _)) => !matches!(c, List::Nil),
        Err(r) => matches!(r, Refusal::Place(_)),
    }
}

/// An expression whose `&&` or `||` has a call or a write on its right side, or whose `?:` has one in a branch, at the top of the
/// expression. C++ runs such a part only sometimes.
pub open spec fn spec_cond_calls(e: Expr, all: Fns, line: u32, sd: Structs) -> bool
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => (op == BinOp::And || op == BinOp::Or) && (spec_needs_if(*b, all, line, sd) || spec_cond_calls(*a, all, line, sd)),
        Expr::Cond(_, a, b) => spec_needs_if(*a, all, line, sd) || spec_needs_if(*b, all, line, sd),
        Expr::Paren(a) => spec_cond_calls(*a, all, line, sd),
        _ => false,
    }
}

pub fn cond_calls(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_cond_calls(*e, *all, line, *sd),
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => (*op == BinOp::And || *op == BinOp::Or) && (needs_if(b, all, line, sd) || cond_calls(a, all, line, sd)),
        Expr::Cond(_, a, b) => needs_if(a, all, line, sd) || needs_if(b, all, line, sd),
        Expr::Paren(a) => cond_calls(a, all, line, sd),
        _ => false,
    }
}

/// The statement that takes the value of a part: the return, or the temporary `t`.
pub open spec fn spec_sink(sink: Option<u32>, res: bool, d: DExpr) -> DStmt {
    match sink {
        None => if res { DStmt::SetResult(d) } else { DStmt::Return(d) },
        Some(t) => DStmt::AssignTemp(t, d),
    }
}

pub fn sink_of(sink: Option<u32>, res: bool, d: DExpr) -> (r: DStmt)
    ensures
        r == spec_sink(sink, res, d),
{
    match sink {
        None => if res { DStmt::SetResult(d) } else { DStmt::Return(d) },
        Some(t) => DStmt::AssignTemp(t, d),
    }
}

/// A `return` whose `&&`, `||` or `?:` runs a call or a write only sometimes, as statements, decision 0177. `a && b` gives the
/// temporary `t` the value of `a`, then of `b` only when `t` holds. `a || b` runs `b` only when `t` does not hold. `c ? a : b`
/// gives each branch its own statements. The temporary takes its number before the calls of the left side. Each statement keeps
/// the place of the `return`.
pub open spec fn spec_lower(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32) -> Result<(DStmts, u32), Refusal>
    decreases e,
{
    match e {
        Expr::Paren(a) => spec_lower(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) {
            if n >= 0xFFFF_FFFF {
                Err(Refusal::Syntax(line))
            } else {
                let t = match sink { Some(t) => t, None => n };
                let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
                match spec_lower(*a, Some(t), res, all, line, sd, n0) {
                    Err(r) => Err(r),
                    Ok((sa, n1)) => match spec_lower(*b, Some(t), res, all, line, sd, n1) {
                        Err(r) => Err(r),
                        Ok((sb, n2)) => {
                            let test = if op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
                            let body = spec_append(sa, List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil)));
                            match sink {
                                Some(_) => Ok((body, n2)),
                                None => Ok((
                                    List::Cons((Box::new(DStmt::DeclTemp(t, DTy::Bool)), line), Box::new(spec_append(body, List::Cons((Box::new(spec_sink(None, res, DExpr::Temp(t))), line), Box::new(List::Nil))))),
                                    n2,
                                )),
                            }
                        },
                    },
                }
            }
        } else {
            spec_lower_leaf(e, sink, res, all, line, sd, n)
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            match spec_lift(*c, all, line, sd, n, true) {
                Err(r) => Err(r),
                Ok((cc, dc, n1)) => match spec_lower(*a, sink, res, all, line, sd, n1) {
                    Err(r) => Err(r),
                    Ok((sa, n2)) => match spec_lower(*b, sink, res, all, line, sd, n2) {
                        Err(r) => Err(r),
                        Ok((sb, n3)) => Ok((List::Cons((Box::new(spec_pre(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)))), line), Box::new(List::Nil)), n3)),
                    },
                },
            }
        } else {
            spec_lower_leaf(e, sink, res, all, line, sd, n)
        },
        _ => spec_lower_leaf(e, sink, res, all, line, sd, n),
    }
}

/// A part with no such `&&`, `||` or `?:` at its top: its calls run first, then the sink takes its value.
pub open spec fn spec_lower_leaf(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32) -> Result<(DStmts, u32), Refusal> {
    match spec_lift(e, all, line, sd, n, true) {
        Err(r) => Err(r),
        Ok((c, d, n1)) => Ok((List::Cons((Box::new(spec_pre(c, spec_sink(sink, res, d))), line), Box::new(List::Nil)), n1)),
    }
}

pub fn lower_leaf(e: &Expr, sink: Option<u32>, res: bool, all: &Fns, line: u32, sd: &Structs, n: u32) -> (r: Result<(DStmts, u32), Refusal>)
    ensures
        r == spec_lower_leaf(*e, sink, res, *all, line, *sd, n),
{
    match lift(e, all, line, sd, n, true) {
        Err(r) => Err(r),
        Ok((c, d, n1)) => Ok((List::Cons((Box::new(pre(c, sink_of(sink, res, d))), line), Box::new(List::Nil)), n1)),
    }
}

pub fn lower(e: &Expr, sink: Option<u32>, res: bool, all: &Fns, line: u32, sd: &Structs, n: u32) -> (r: Result<(DStmts, u32), Refusal>)
    ensures
        r == spec_lower(*e, sink, res, *all, line, *sd, n),
    decreases e,
{
    match e {
        Expr::Paren(a) => lower(a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (*op == BinOp::And || *op == BinOp::Or) && cond_calls(e, all, line, sd) {
            if n == 0xFFFF_FFFF {
                Err(Refusal::Syntax(line))
            } else {
                let t = match sink { Some(t) => t, None => n };
                let n0: u32 = if sink.is_none() { n + 1 } else { n };
                match lower(a, Some(t), res, all, line, sd, n0) {
                    Err(r) => Err(r),
                    Ok((sa, n1)) => match lower(b, Some(t), res, all, line, sd, n1) {
                        Err(r) => Err(r),
                        Ok((sb, n2)) => {
                            let test = if *op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
                            let body = append(sa, List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil)));
                            match sink {
                                Some(_) => Ok((body, n2)),
                                None => Ok((
                                    List::Cons((Box::new(DStmt::DeclTemp(t, DTy::Bool)), line), Box::new(append(body, List::Cons((Box::new(sink_of(None, res, DExpr::Temp(t))), line), Box::new(List::Nil))))),
                                    n2,
                                )),
                            }
                        },
                    },
                }
            }
        } else {
            lower_leaf(e, sink, res, all, line, sd, n)
        },
        Expr::Cond(c, a, b) => if cond_calls(e, all, line, sd) {
            match lift(c, all, line, sd, n, true) {
                Err(r) => Err(r),
                Ok((cc, dc, n1)) => match lower(a, sink, res, all, line, sd, n1) {
                    Err(r) => Err(r),
                    Ok((sa, n2)) => match lower(b, sink, res, all, line, sd, n2) {
                        Err(r) => Err(r),
                        Ok((sb, n3)) => Ok((List::Cons((Box::new(pre(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)))), line), Box::new(List::Nil)), n3)),
                    },
                },
            }
        } else {
            lower_leaf(e, sink, res, all, line, sd, n)
        },
        _ => lower_leaf(e, sink, res, all, line, sd, n),
    }
}

/// Each call of a lowered `return` names a key with a method.
pub proof fn lemma_lower_resolves(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lower(e, sink, res, all, line, sd, n).is_ok(),
    ensures
        calls_resolve(spec_lower(e, sink, res, all, line, sd, n).unwrap().0, all, sd),
    decreases e,
{
    reveal_with_fuel(calls_resolve, 3);
    match e {
        Expr::Paren(a) => lemma_lower_resolves(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) {
            let t = match sink { Some(t) => t, None => n };
            let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
            lemma_lower_resolves(*a, Some(t), res, all, line, sd, n0);
            let (sa, n1) = spec_lower(*a, Some(t), res, all, line, sd, n0).unwrap();
            lemma_lower_resolves(*b, Some(t), res, all, line, sd, n1);
            let (sb, _) = spec_lower(*b, Some(t), res, all, line, sd, n1).unwrap();
            let test = if op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
            let tail = List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil));
            lemma_resolve_append(sa, tail, all, sd);
            let body = spec_append(sa, tail);
            let ret = List::Cons((Box::new(spec_sink(None, res, DExpr::Temp(t))), line), Box::new(List::Nil));
            lemma_resolve_append(body, ret, all, sd);
        } else {
            lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n);
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            lemma_lift_resolves(*c, all, line, sd, n, true);
            let (cc, dc, n1) = spec_lift(*c, all, line, sd, n, true).unwrap();
            lemma_lower_resolves(*a, sink, res, all, line, sd, n1);
            let (sa, n2) = spec_lower(*a, sink, res, all, line, sd, n1).unwrap();
            lemma_lower_resolves(*b, sink, res, all, line, sd, n2);
            let (sb, _) = spec_lower(*b, sink, res, all, line, sd, n2).unwrap();
            lemma_pre_resolves(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)), all, sd);
        } else {
            lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n);
        },
        _ => lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n),
    }
}

pub proof fn lemma_lower_leaf_resolves(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lower_leaf(e, sink, res, all, line, sd, n).is_ok(),
    ensures
        calls_resolve(spec_lower_leaf(e, sink, res, all, line, sd, n).unwrap().0, all, sd),
{
    reveal_with_fuel(calls_resolve, 2);
    lemma_lift_resolves(e, all, line, sd, n, true);
    let (c, d, _) = spec_lift(e, all, line, sd, n, true).unwrap();
    lemma_pre_resolves(c, spec_sink(sink, res, d), all, sd);
}

/// The calls of two lists of statements resolve when the calls of each do.
pub proof fn lemma_resolve_append(a: DStmts, b: DStmts, all: Fns, sd: Structs)
    ensures
        calls_resolve(spec_append(a, b), all, sd) == (calls_resolve(a, all, sd) && calls_resolve(b, all, sd)),
    decreases a,
{
    match a {
        List::Nil => {},
        List::Cons(_, rest) => lemma_resolve_append(*rest, b, all, sd),
    }
}

/// A lowered `return` with a node that has no rule is refused.
pub proof fn lemma_unknown_lower_is_refused(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        unknown_expr(e),
    ensures
        spec_lower(e, sink, res, all, line, sd, n).is_err(),
    decreases e,
{
    match e {
        Expr::Paren(a) => lemma_unknown_lower_is_refused(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) && n < 0xFFFF_FFFF {
            let t = match sink { Some(t) => t, None => n };
            let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
            if unknown_expr(*a) {
                lemma_unknown_lower_is_refused(*a, Some(t), res, all, line, sd, n0);
            } else if spec_lower(*a, Some(t), res, all, line, sd, n0).is_ok() {
                lemma_unknown_lower_is_refused(*b, Some(t), res, all, line, sd, spec_lower(*a, Some(t), res, all, line, sd, n0).unwrap().1);
            }
        } else if !((op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd)) {
            lemma_unknown_lift_is_refused(e, all, line, sd, n, true);
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            if unknown_expr(*c) {
                lemma_unknown_lift_is_refused(*c, all, line, sd, n, true);
            } else if spec_lift(*c, all, line, sd, n, true).is_ok() {
                let n1 = spec_lift(*c, all, line, sd, n, true).unwrap().2;
                if unknown_expr(*a) {
                    lemma_unknown_lower_is_refused(*a, sink, res, all, line, sd, n1);
                } else if spec_lower(*a, sink, res, all, line, sd, n1).is_ok() {
                    lemma_unknown_lower_is_refused(*b, sink, res, all, line, sd, spec_lower(*a, sink, res, all, line, sd, n1).unwrap().1);
                }
            }
        } else {
            lemma_unknown_lift_is_refused(e, all, line, sd, n, true);
        },
        _ => lemma_unknown_lift_is_refused(e, all, line, sd, n, true),
    }
}

} // verus!

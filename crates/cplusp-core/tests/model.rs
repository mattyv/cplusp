//! The translator core on the shapes of `examples/saturating_add`, decisions 0056 and 0058. The proofs in src/model.rs say that each
//! function computes its rule. These tests pin what the rules give for real functions, and for each refusal.

use cplusp_core::model::*;

const X: u32 = 1;
const LO: u32 = 2;
const HI: u32 = 3;
const CLAMP: u32 = 10;
const CALL_EXPR: u32 = 20;
const SUM: u32 = 30;
const A: u32 = 31;
const B: u32 = 32;
const SAT: u32 = 40;
const SAT_NAME: u32 = 41;
const SUCC: u32 = 42;
const OTHER_TYPE: u32 = 50;
const P: u32 = 60;
const Q: u32 = 61;

fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}

fn var(n: u32) -> Expr {
    Expr::Var(n, Ty::I32)
}

/// The names of the parameters of the declaration that a contract line stands on.
fn names(v: &[u32]) -> Names {
    v.iter().rev().fold(List::Nil, |rest, n| List::Cons(*n, Box::new(rest)))
}

/// The places of a body set to 0. A test of what a rule gives compares with this. One test pins the places, decision 0068.
fn strip(ss: DStmts) -> DStmts {
    match ss {
        List::Nil => List::Nil,
        List::Cons((s, _), rest) => List::Cons((Box::new(strip_stmt(*s)), 0), Box::new(strip(*rest))),
    }
}

fn strip_stmt(s: DStmt) -> DStmt {
    match s {
        DStmt::If(c, t, f) => DStmt::If(c, Box::new(strip(*t)), Box::new(strip(*f))),
        DStmt::While(c, i, d, b) => DStmt::While(c, strip_conds(i), strip_conds(d), Box::new(strip(*b))),
        DStmt::For(init, _, c, i, d, b, step, _) => DStmt::For(
            Box::new(strip_stmt(*init)),
            0,
            c,
            strip_conds(i),
            strip_conds(d),
            Box::new(strip(*b)),
            Box::new(strip_stmt(*step)),
            0,
        ),
        DStmt::Block(b) => DStmt::Block(Box::new(strip(*b))),
        DStmt::Scope(b) => DStmt::Scope(Box::new(strip(*b))),
        DStmt::Dtors(b) => DStmt::Dtors(Box::new(strip(*b))),
        DStmt::Pre(c, x) => DStmt::Pre(c, Box::new(strip_stmt(*x))),
        other => other,
    }
}

fn strip_conds(cs: DConds) -> DConds {
    match cs {
        List::Nil => List::Nil,
        List::Cons((e, _), rest) => List::Cons((e, 0), Box::new(strip_conds(*rest))),
    }
}

/// A literal of code prints with its type, decision 0061.
fn lit32(n: u64) -> DExpr {
    DExpr::Conv(DTy::Int32, Box::new(DExpr::Lit(n)))
}

fn params() -> Params {
    List::Cons((X, Ty::I32), Box::new(List::Cons((LO, Ty::I32), Box::new(List::Cons((HI, Ty::I32), Box::new(List::Nil))))))
}

#[test]
fn a_contract_line_parses_with_the_precedence_of_the_contract_language() {
    // x < lo ==> result == lo
    let toks = vec![Tok::Ident(X), Tok::Op(BinOp::Lt), Tok::Ident(LO), Tok::Op(BinOp::Implies), Tok::Result, Tok::Op(BinOp::Eq), Tok::Ident(LO)];
    let e = parse_contract(&toks, 4).unwrap();
    assert_eq!(
        e,
        Expr::Bin(
            BinOp::Implies,
            b(Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Name(LO)))),
            b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(LO))))
        )
    );
}

#[test]
fn a_contract_line_that_does_not_end_cleanly_is_refused() {
    let toks = vec![Tok::Ident(X), Tok::Op(BinOp::Lt)];
    assert_eq!(parse_contract(&toks, 7), Err(Refusal::Syntax(7)));
    let toks = vec![Tok::LParen, Tok::Ident(X)];
    assert_eq!(parse_contract(&toks, 8), Err(Refusal::Syntax(8)));
    let toks = vec![Tok::Ident(X), Tok::Ident(LO)];
    assert_eq!(parse_contract(&toks, 9), Err(Refusal::Syntax(9)));
}

#[test]
fn a_token_with_no_rule_is_refused_by_its_kind_wherever_it_is() {
    // x > 0 $ : the parser would stop before the `$` and call the line bad syntax. The token names the problem.
    let dollar = 77;
    let toks = vec![Tok::Ident(X), Tok::Op(BinOp::Gt), Tok::Int(0), Tok::Unknown(dollar, 6)];
    assert_eq!(parse_contract(&toks, 6), Err(Refusal::Construct(dollar, 6)));
    // result = x
    let toks = vec![Tok::Result, Tok::Unknown(dollar, 7), Tok::Ident(X)];
    assert_eq!(parse_contract(&toks, 7), Err(Refusal::Construct(dollar, 7)));
}

#[test]
fn clamp_translates_to_a_method_whose_contract_reads_exact_integers() {
    // requires lo <= hi; ensures x < lo ==> result == lo; if (x < lo) { return lo; } return x;
    let conds = List::Cons((CondKind::Requires, Expr::Bin(BinOp::Le, b(Expr::Name(LO)), b(Expr::Name(HI))), 21, names(&[X, LO, HI])), Box::new(List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Implies, b(Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Name(LO)))), b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(LO))))), 22, names(&[X, LO, HI])), Box::new(List::Nil))));
    let body = List::Cons(
        Box::new(Stmt::If(
            Expr::Bin(BinOp::Lt, b(var(X)), b(var(LO))),
            Box::new(List::Cons(Box::new(Stmt::Return(var(LO), 28)), Box::new(List::Nil))),
            Box::new(List::Nil),
            27,
        )),
        Box::new(List::Cons(Box::new(Stmt::Return(var(X), 30)), Box::new(List::Nil))));
    let f = Function { name: CLAMP, line: 26, params: params(), ret: Ty::I32, trusted: false, conds, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("clamp has a full model") };
    let as_int = |n: u32| DExpr::AsInt(Box::new(DExpr::Var(n)));
    assert_eq!(strip_conds(m.requires), List::Cons((DExpr::Bin(BinOp::Le, Box::new(as_int(LO)), Box::new(as_int(HI))), 0), Box::new(List::Nil)));
    assert_eq!(
        strip_conds(m.ensures),
        List::Cons((DExpr::Bin(
                BinOp::Implies,
                Box::new(DExpr::Bin(BinOp::Lt, Box::new(as_int(X)), Box::new(as_int(LO)))),
                Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(as_int(LO))))
            ), 0), Box::new(List::Nil))
    );
    // The body keeps the machine operators: no `as int` in code.
    assert_eq!(
        strip(m.body),
        List::Cons((Box::new(DStmt::If(
                DExpr::Bin(BinOp::Lt, Box::new(DExpr::Var(X)), Box::new(DExpr::Var(LO))),
                Box::new(List::Cons((Box::new(DStmt::Return(DExpr::Var(LO))), 0), Box::new(List::Nil))),
                Box::new(List::Nil)
            )), 0), Box::new(List::Cons((Box::new(DStmt::Return(DExpr::Var(X))), 0), Box::new(List::Nil))))
    );
    assert_eq!(m.ret, DTy::Int32);
}

fn one(s: Stmt) -> Stmts {
    List::Cons(Box::new(s), Box::new(List::Nil))
}

fn fns(v: Vec<Function>) -> Fns {
    v.into_iter().rev().fold(List::Nil, |rest, f| List::Cons(Box::new(f), Box::new(rest)))
}

fn read(n: u32, t: Ty) -> Expr {
    Expr::Cast(CastKind::Read, b(Expr::Var(n, t)))
}

/// `int32_t saturating_add(int32_t a, int32_t b)`, with a body of `body`.
fn sat(body: Stmts) -> Function {
    let ps = List::Cons((A, Ty::I32), Box::new(List::Cons((B, Ty::I32), Box::new(List::Nil))));
    Function { name: SAT, line: 10, params: ps, ret: Ty::I32, trusted: false, conds: List::Nil, body }
}

/// `int32_t successor(int32_t x) { return <e>; }`
fn succ(e: Expr) -> Function {
    Function { name: SUCC, line: 37, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(e, 38)) }
}

fn call(key: u32, args: Vec<Expr>, line: u32) -> Expr {
    let args = args.into_iter().rev().fold(List::Nil, |rest, e| List::Cons(Box::new(e), Box::new(rest)));
    Expr::Call(key, SAT_NAME, Box::new(args), line)
}

/// The refusal of a function whose signature is in the subset: a method with no contract and no body, and the refusal.
fn bare_refusal(m: Model) -> Refusal {
    match m {
        Model::Bare(_, _, _, r) => r,
        other => panic!("not a bare model: {other:?}"),
    }
}

#[test]
fn a_local_and_integral_casts_translate_to_dafny_casts_that_dafny_checks() {
    // int64_t sum = int64_t{a} + b; return static_cast<int32_t>(sum);
    let widen = |n: u32| Expr::Cast(CastKind::Integral(Ty::I32, Ty::I64), b(read(n, Ty::I32)));
    let sum = Expr::Bin(BinOp::Add, b(Expr::Cast(CastKind::NoOp, b(Expr::Brace(b(widen(A)))))), b(widen(B)));
    let back = Expr::Cast(CastKind::NoOp, b(Expr::Cast(CastKind::Integral(Ty::I64, Ty::I32), b(read(SUM, Ty::I64)))));
    let body = List::Cons(Box::new(Stmt::Local(SUM, Ty::I64, sum, 11)), Box::new(one(Stmt::Return(back, 18))));
    let Model::Full(m) = translate_function(&sat(body), &List::Nil, &List::Nil) else { panic!("saturating_add has a full model") };
    let conv = |t: DTy, d: DExpr| DExpr::Conv(t, Box::new(d));
    let dsum = DExpr::Bin(BinOp::Add, Box::new(conv(DTy::Int64, DExpr::Var(A))), Box::new(conv(DTy::Int64, DExpr::Var(B))));
    assert_eq!(
        strip(m.body),
        List::Cons((Box::new(DStmt::Local(SUM, DTy::Int64, dsum)), 0), Box::new(List::Cons((Box::new(DStmt::Return(conv(DTy::Int32, DExpr::Var(SUM)))), 0), Box::new(List::Nil))))
    );
}

#[test]
fn a_call_that_stands_alone_names_the_method_of_its_callee() {
    // successor: return saturating_add(x, 1); and a local whose start value is the call.
    let all = fns(vec![sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))), succ(call(SAT, vec![read(X, Ty::I32), Expr::Lit(1, Ty::I32)], 38))]);
    let List::Cons(_, rest) = translate_unit(&all, &List::Nil) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("successor has a full model") };
    let args = List::Cons(DExpr::Var(X), Box::new(List::Cons(lit32(1), Box::new(List::Nil))));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::ReturnCall(SAT, args)), 0), Box::new(List::Nil)));

    let local = Stmt::Local(A, Ty::I32, call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 39), 39);
    let f = Function { body: List::Cons(Box::new(local), Box::new(one(Stmt::Return(read(A, Ty::I32), 40)))), ..succ(Expr::Lit(0, Ty::I32)) };
    let Model::Full(m) = translate_function(&f, &all, &List::Nil) else { panic!("a local from a call has a full model") };
    let List::Cons((first, _), _) = m.body else { panic!("a body") };
    let args = List::Cons(lit32(1), Box::new(List::Cons(lit32(2), Box::new(List::Nil))));
    assert_eq!(*first, DStmt::LocalCall(A, DTy::Int32, SAT, args));
}

#[test]
fn a_call_inside_an_expression_runs_before_its_statement() {
    let all = fns(vec![sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)))]);
    let c = |l: u32| call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], l);
    let args = || List::Cons(lit32(1), Box::new(List::Cons(lit32(2), Box::new(List::Nil))));
    let run = |t: u32, a: DArgs, rest: DCalls| List::Cons(DPre::Call(t, DTy::Int32, SAT, a), Box::new(rest));
    // return sat(1, 2) + 1;
    let plus = Expr::Bin(BinOp::Add, b(c(38)), b(Expr::Lit(1, Ty::I32)));
    let Model::Full(m) = translate_function(&succ(plus), &all, &List::Nil) else { panic!("a full model") };
    let want = DStmt::Pre(run(0, args(), List::Nil), Box::new(DStmt::Return(DExpr::Bin(BinOp::Add, Box::new(DExpr::Temp(0)), Box::new(lit32(1))))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    // return sat(sat(1, 2), 2); the inner call runs first.
    let nested = call(SAT, vec![c(39), Expr::Lit(2, Ty::I32)], 39);
    let Model::Full(m) = translate_function(&succ(nested), &all, &List::Nil) else { panic!("a full model") };
    let outer = List::Cons(DExpr::Temp(0), Box::new(List::Cons(lit32(2), Box::new(List::Nil))));
    let want = DStmt::Pre(run(0, args(), List::Nil), Box::new(DStmt::ReturnCall(SAT, outer)));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    // if (sat(1, 2) + sat(1, 2) > 0) {}: two calls in the order of the source, numbered 0 and 1.
    let two = Expr::Bin(BinOp::Gt, b(Expr::Bin(BinOp::Add, b(c(40)), b(c(40)))), b(Expr::Lit(0, Ty::I32)));
    let body = List::Cons(Box::new(Stmt::If(two, Box::new(List::Nil), Box::new(List::Nil), 40)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 41))));
    let f = Function { body, ..succ(Expr::Lit(0, Ty::I32)) };
    let Model::Full(m) = translate_function(&f, &all, &List::Nil) else { panic!("a full model") };
    let List::Cons((first, _), _) = strip(m.body) else { panic!("a body") };
    let cond = DExpr::Bin(BinOp::Gt, Box::new(DExpr::Bin(BinOp::Add, Box::new(DExpr::Temp(0)), Box::new(DExpr::Temp(1)))), Box::new(lit32(0)));
    let want = DStmt::Pre(run(0, args(), run(1, args(), List::Nil)), Box::new(DStmt::If(cond, Box::new(List::Nil), Box::new(List::Nil))));
    assert_eq!(*first, want);
}

#[test]
fn a_call_that_cpp_may_not_evaluate_once_is_refused_at_its_line() {
    let all = fns(vec![sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)))]);
    let args = || List::Cons(lit32(1), Box::new(List::Cons(lit32(2), Box::new(List::Nil))));
    let c = |l: u32| call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], l);
    let positive = |l: u32| Expr::Bin(BinOp::Gt, b(c(l)), b(Expr::Lit(0, Ty::I32)));
    let with = |s: Stmt| Function { body: List::Cons(Box::new(s), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 50)))), ..succ(Expr::Lit(0, Ty::I32)) };
    // if (true && sat(1, 2) > 0) {}: the right of && may not run.
    let and = Expr::Bin(BinOp::And, b(Expr::Bool(true)), b(positive(42)));
    let f = with(Stmt::If(and, Box::new(List::Nil), Box::new(List::Nil), 42));
    assert_eq!(bare_refusal(translate_function(&f, &all, &List::Nil)), Refusal::Place(42));
    // return true ? sat(1, 2) : 0; a branch may not run, so each branch returns its own value, decision 0177.
    let branch = Expr::Cond(b(Expr::Bool(true)), b(c(44)), b(Expr::Lit(0, Ty::I32)));
    let Model::Full(m) = translate_function(&succ(branch), &all, &List::Nil) else { panic!("a full model") };
    let List::Cons((s, _), _) = strip(m.body) else { panic!("a body") };
    let then = List::Cons((Box::new(DStmt::Pre(List::Cons(DPre::Call(0, DTy::Int32, SAT, args()), Box::new(List::Nil)), Box::new(DStmt::Return(DExpr::Temp(0))))), 0), Box::new(List::Nil));
    let other = List::Cons((Box::new(DStmt::Return(lit32(0))), 0), Box::new(List::Nil));
    assert_eq!(*s, DStmt::Block(Box::new(List::Cons((Box::new(DStmt::If(DExpr::Bool(true), Box::new(then), Box::new(other))), 0), Box::new(List::Nil)))));
    // while (sat(1, 2) > 0) {}: a loop condition runs again at each turn.
    let f = with(Stmt::While(positive(46), Box::new(List::Nil), Box::new(List::Nil), 46));
    assert_eq!(bare_refusal(translate_function(&f, &all, &List::Nil)), Refusal::Place(46));
}

#[test]
fn a_call_to_a_function_with_no_method_is_refused_by_the_callee_name() {
    let to_sat = succ(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 38));
    // No such function in the unit.
    assert_eq!(bare_refusal(translate_function(&to_sat, &List::Nil, &List::Nil)), Refusal::Callee(SAT_NAME, 38));
    // The callee is in the unit, but its signature is not in the subset, so it has no method.
    let odd = Function { ret: Ty::Other(OTHER_TYPE), ..sat(List::Nil) };
    let all = fns(vec![odd, to_sat]);
    let List::Cons(first, rest) = translate_unit(&all, &List::Nil) else { panic!("two models") };
    assert_eq!(first, Model::Refused(Refusal::Construct(OTHER_TYPE, 10)));
    let List::Cons(second, _) = *rest else { panic!("two models") };
    assert_eq!(bare_refusal(second), Refusal::Callee(SAT_NAME, 38));
}

#[test]
fn a_callee_whose_body_is_refused_keeps_a_method_with_no_contract() {
    let conds = List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))), 9, names(&[A, B])), Box::new(List::Nil));
    let refused = Function { conds, ..sat(one(Stmt::Return(Expr::Unknown(CALL_EXPR, 11), 11))) };
    let all = fns(vec![refused, succ(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 38))]);
    let List::Cons(first, rest) = translate_unit(&all, &List::Nil) else { panic!("two models") };
    let Model::Bare(name, params, ret, r) = first else { panic!("a bare model: {first:?}") };
    assert_eq!((name, ret, r), (SAT, DTy::Int32, Refusal::Construct(CALL_EXPR, 11)));
    assert_eq!(params, List::Cons((A, DTy::Int32), Box::new(List::Cons((B, DTy::Int32), Box::new(List::Nil)))));
    let List::Cons(Model::Full(_), _) = *rest else { panic!("the caller has a full model") };
}

#[test]
fn a_contract_line_the_shell_could_not_read_keeps_the_signature() {
    let conds = List::Cons((CondKind::Bad(Refusal::Syntax(9)), Expr::Int(0), 9, List::Nil), Box::new(List::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(9));
    let conds = List::Cons((CondKind::Bad(Refusal::Backslash(8)), Expr::Int(0), 8, List::Nil), Box::new(List::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Backslash(8));
}

#[test]
fn each_name_is_declared_once_in_a_function() {
    // int32_t a = 1; in a function with a parameter a.
    let f = sat(List::Cons(Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(1, Ty::I32), 12)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)))));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Twice(A, 12));
    // int32_t sum = 1; if (..) { int32_t sum = 2; }
    let inner = Stmt::If(Expr::Bin(BinOp::Lt, b(read(A, Ty::I32)), b(Expr::Lit(0, Ty::I32))), Box::new(one(Stmt::Local(SUM, Ty::I64, Expr::Lit(2, Ty::I32), 14))), Box::new(List::Nil), 14);
    let body = List::Cons(Box::new(Stmt::Local(SUM, Ty::I64, Expr::Lit(1, Ty::I32), 13)), Box::new(List::Cons(Box::new(inner), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))))));
    assert_eq!(bare_refusal(translate_function(&sat(body), &List::Nil, &List::Nil)), Refusal::Twice(SUM, 14));
}

#[test]
fn a_conversion_between_bool_and_a_number_is_refused() {
    let to_bool = Expr::Cast(CastKind::Integral(Ty::Bool, Ty::I32), b(Expr::Var(A, Ty::Bool)));
    // A refusal inside an expression is at the line of its statement.
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(to_bool, 12))), &List::Nil, &List::Nil)), Refusal::Convert(12));
    // A type with no rule inside a cast is refused by that type, before the bool rule.
    let odd = Expr::Cast(CastKind::Integral(Ty::Other(OTHER_TYPE), Ty::I32), b(Expr::Var(A, Ty::I32)));
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(odd, 13))), &List::Nil, &List::Nil)), Refusal::Construct(OTHER_TYPE, 13));
}

#[test]
fn a_node_with_no_rule_is_refused_with_its_kind_and_line() {
    let body = List::Cons(Box::new(Stmt::Return(Expr::Unknown(CALL_EXPR, 38), 38)), Box::new(List::Nil));
    let f = Function { name: CLAMP, line: 37, params: params(), ret: Ty::I32, trusted: false, conds: List::Nil, body };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Construct(CALL_EXPR, 38));
}

#[test]
fn a_contract_name_that_is_no_parameter_is_refused() {
    let conds = List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(99))), 5, names(&[X, LO, HI])), Box::new(List::Nil));
    let f = Function { name: CLAMP, line: 6, params: params(), ret: Ty::I32, trusted: false, conds, body: List::Nil };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Name(99, 5));
}

#[test]
fn a_signature_outside_the_subset_has_no_method() {
    let f = Function { ret: Ty::Other(OTHER_TYPE), ..sat(List::Nil) };
    assert_eq!(translate_function(&f, &List::Nil, &List::Nil), Model::Refused(Refusal::Construct(OTHER_TYPE, 10)));
}

#[test]
fn a_literal_of_a_type_outside_the_subset_is_refused() {
    // return -1u < 1u; C++ wraps the negation, so a literal that lost its type would give the wrong result.
    let unsigned = |n: u64| Expr::Lit(n, Ty::Other(OTHER_TYPE));
    let e = Expr::Bin(BinOp::Lt, b(Expr::Neg(b(unsigned(1)))), b(unsigned(1)));
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(e, 6))), &List::Nil, &List::Nil)), Refusal::Construct(OTHER_TYPE, 6));
}

#[test]
fn a_contract_reads_the_parameters_of_its_declaration_by_place() {
    // int32_t sat(int32_t p, int32_t q) with ensures result == p - q, and the definition sat(int32_t a, int32_t b).
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Sub, b(Expr::Name(P)), b(Expr::Name(Q)))));
    let conds = List::Cons((CondKind::Ensures, ens, 9, names(&[P, Q])), Box::new(List::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let as_int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Bin(BinOp::Eq, as_int(DExpr::Result), Box::new(DExpr::Bin(BinOp::Sub, as_int(DExpr::Var(A)), as_int(DExpr::Var(B)))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // The declaration says (b, a). Its `a` is the definition's second parameter, `b`, and its `b` is the first, `a`.
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Sub, b(Expr::Name(A)), b(Expr::Name(B)))));
    let conds = List::Cons((CondKind::Ensures, ens, 9, names(&[B, A])), Box::new(List::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Eq, as_int(DExpr::Result), Box::new(DExpr::Bin(BinOp::Sub, as_int(DExpr::Var(B)), as_int(DExpr::Var(A)))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A name of the definition that the declaration does not have is no parameter of the contract.
    let conds = List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(A))), 9, names(&[P, Q])), Box::new(List::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Name(A, 9));
}

/// `int32_t n` alone, with a body.
fn with_n(body: Stmts) -> Function {
    Function { name: SAT, line: 3, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body }
}

fn conds(v: Vec<(CondKind, Expr, u32)>) -> Conds {
    v.into_iter().rev().fold(List::Nil, |rest, (k, e, l)| List::Cons((k, e, l, List::Nil), Box::new(rest)))
}

#[test]
fn a_literal_of_code_carries_its_type_into_dafny() {
    let m = translate_function(&with_n(one(Stmt::Return(Expr::Lit(7, Ty::I32), 4))), &List::Nil, &List::Nil);
    let Model::Full(m) = m else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(lit32(7))), 0), Box::new(List::Nil)));
    // The unsigned types of decision 0061.
    let m = translate_function(&with_n(one(Stmt::Return(Expr::Lit(7, Ty::U64), 4))), &List::Nil, &List::Nil);
    let Model::Full(m) = m else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(7))))), 0), Box::new(List::Nil)));
}

#[test]
fn a_for_loop_is_its_start_then_a_while_that_ends_with_its_step() {
    // int32_t i = 0; invariant i <= n; decreases n - i; for (...; i < n; ++i) { acc = acc + 1; }
    let i = SUM;
    let acc = A;
    let start = Stmt::Local(i, Ty::I32, Expr::Lit(0, Ty::I32), 5);
    let cond = Expr::Bin(BinOp::Lt, b(read(i, Ty::I32)), b(read(X, Ty::I32)));
    let step = Stmt::Step(i, Ty::I32, true, 7);
    let loop_conds = conds(vec![
        (CondKind::Invariant, Expr::Bin(BinOp::Le, b(Expr::Name(i)), b(Expr::Name(X))), 5),
        (CondKind::Decreases, Expr::Bin(BinOp::Sub, b(Expr::Name(X)), b(Expr::Name(i))), 6),
    ]);
    let write = Stmt::Assign(acc, Expr::Bin(BinOp::Add, b(read(acc, Ty::I32)), b(Expr::Lit(1, Ty::I32))), 8);
    let lp = Stmt::For(Box::new(start), cond, Box::new(step), Box::new(loop_conds), Box::new(one(write)), 7);
    let body = List::Cons(
        Box::new(Stmt::Local(acc, Ty::I32, Expr::Lit(0, Ty::I32), 4)),
        Box::new(List::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(acc, Ty::I32), 10))))));
    let Model::Full(m) = translate_function(&with_n(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((_, _), rest) = m.body else { panic!("a body") };
    let List::Cons((lp, _), _) = *rest else { panic!("a loop") };
    let as_int = |n: u32| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    // The start and the step keep their own places, 5 and 7, decision 0069.
    let DStmt::For(_, start_at, _, _, _, _, _, step_at) = &*lp else { panic!("a for loop") };
    assert_eq!((*start_at, *step_at), (5, 7));
    let want = DStmt::For(
        Box::new(DStmt::Local(i, DTy::Int32, lit32(0))),
        0,
        DExpr::Bin(BinOp::Lt, Box::new(DExpr::Var(i)), Box::new(DExpr::Var(X))),
        List::Cons((DExpr::Bin(BinOp::Le, as_int(i), as_int(X)), 0), Box::new(List::Nil)),
        List::Cons((DExpr::Bin(BinOp::Sub, as_int(X), as_int(i)), 0), Box::new(List::Nil)),
        Box::new(List::Cons((Box::new(DStmt::Assign(acc, DExpr::Bin(BinOp::Add, Box::new(DExpr::Var(acc)), Box::new(lit32(1))))), 0), Box::new(List::Nil))),
        Box::new(DStmt::Assign(i, DExpr::Bin(BinOp::Add, Box::new(DExpr::Var(i)), Box::new(lit32(1))))),
        0,
    );
    assert_eq!(strip_stmt(*lp), want);
}

#[test]
fn a_while_loop_reads_its_contract_over_parameters_and_locals() {
    // int32_t k = n; invariant 0 <= k; decreases k; while (k > 0) { --k; }
    let k = SUM;
    let lc = conds(vec![
        (CondKind::Invariant, Expr::Bin(BinOp::Le, b(Expr::Int(0)), b(Expr::Name(k))), 5),
        (CondKind::Decreases, Expr::Name(k), 6),
    ]);
    let lp = Stmt::While(Expr::Bin(BinOp::Gt, b(read(k, Ty::I32)), b(Expr::Lit(0, Ty::I32))), Box::new(lc), Box::new(one(Stmt::Step(k, Ty::I32, false, 8))), 7);
    let body = List::Cons(Box::new(Stmt::Local(k, Ty::I32, read(X, Ty::I32), 4)), Box::new(List::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(k, Ty::I32), 10))))));
    let Model::Full(m) = translate_function(&with_n(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((_, _), rest) = m.body else { panic!("a body") };
    let List::Cons((lp, _), _) = *rest else { panic!("a loop") };
    let kk = || Box::new(DExpr::AsInt(Box::new(DExpr::Var(k))));
    let want = DStmt::While(
        DExpr::Bin(BinOp::Gt, Box::new(DExpr::Var(k)), Box::new(lit32(0))),
        List::Cons((DExpr::Bin(BinOp::Le, Box::new(DExpr::Lit(0)), kk()), 0), Box::new(List::Nil)),
        List::Cons((*kk(), 0), Box::new(List::Nil)),
        Box::new(List::Cons((Box::new(DStmt::Assign(k, DExpr::Bin(BinOp::Sub, Box::new(DExpr::Var(k)), Box::new(lit32(1))))), 0), Box::new(List::Nil))),
    );
    assert_eq!(strip_stmt(*lp), want);
}

#[test]
fn a_write_to_a_parameter_is_refused() {
    let body = List::Cons(Box::new(Stmt::Assign(X, Expr::Lit(1, Ty::I32), 5)), Box::new(one(Stmt::Return(read(X, Ty::I32), 6))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &List::Nil, &List::Nil)), Refusal::WriteParam(X, 5));
    let body = List::Cons(Box::new(Stmt::Step(X, Ty::I32, true, 5)), Box::new(one(Stmt::Return(read(X, Ty::I32), 6))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &List::Nil, &List::Nil)), Refusal::WriteParam(X, 5));
}

#[test]
fn a_loop_contract_names_only_variables_and_never_result() {
    let lp = |lc: Conds| Stmt::While(Expr::Lit(1, Ty::Bool), Box::new(lc), Box::new(List::Nil), 7);
    let f = |lc: Conds| with_n(List::Cons(Box::new(lp(lc)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 9)))));
    let unbound = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Le, b(Expr::Name(X)), b(Expr::Name(99))), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(unbound), &List::Nil, &List::Nil)), Refusal::NoVar(99, 6));
    let result = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(result), &List::Nil, &List::Nil)), Refusal::Syntax(6));
    let ensures = conds(vec![(CondKind::Ensures, Expr::Name(X), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(ensures), &List::Nil, &List::Nil)), Refusal::Misplaced(6));
}

#[test]
fn a_loop_contract_line_above_a_function_is_refused() {
    let fc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(X))), 2)]);
    let f = Function { trusted: false, conds: fc, ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Misplaced(2));
}

#[test]
fn a_name_declared_in_a_loop_counts_for_declared_once() {
    // int32_t i = 0; for (int32_t i = 0; ...) — the start of the for declares i a second time.
    let start = Stmt::Local(SUM, Ty::I32, Expr::Lit(0, Ty::I32), 6);
    let lp = Stmt::For(Box::new(start), Expr::Lit(0, Ty::Bool), Box::new(Stmt::Step(SUM, Ty::I32, true, 6)), Box::new(List::Nil), Box::new(List::Nil), 6);
    let body = List::Cons(Box::new(Stmt::Local(SUM, Ty::I32, Expr::Lit(0, Ty::I32), 5)), Box::new(List::Cons(Box::new(lp), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 7))))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &List::Nil, &List::Nil)), Refusal::Twice(SUM, 6));
}

#[test]
fn a_loop_contract_reads_only_the_variables_in_scope_at_the_loop() {
    // int32_t i = 0; invariant t == 1; while (...) { int32_t t = 1; ++i; }
    let (i, t) = (SUM, A);
    let lc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Name(t)), b(Expr::Int(1))), 5)]);
    let body = List::Cons(Box::new(Stmt::Local(t, Ty::I32, Expr::Lit(1, Ty::I32), 7)), Box::new(one(Stmt::Step(i, Ty::I32, true, 8))));
    let lp = Stmt::While(Expr::Bin(BinOp::Lt, b(read(i, Ty::I32)), b(read(X, Ty::I32))), Box::new(lc), Box::new(body), 6);
    let f = with_n(List::Cons(Box::new(Stmt::Local(i, Ty::I32, Expr::Lit(0, Ty::I32), 4)), Box::new(List::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(i, Ty::I32), 10)))))));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::NoVar(t, 5));
    // A local declared after the loop.
    let lc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Name(t)), b(Expr::Int(1))), 5)]);
    let lp = Stmt::While(Expr::Bin(BinOp::Lt, b(read(i, Ty::I32)), b(read(X, Ty::I32))), Box::new(lc), Box::new(one(Stmt::Step(i, Ty::I32, true, 7))), 6);
    let tail = List::Cons(Box::new(Stmt::Local(t, Ty::I32, Expr::Lit(1, Ty::I32), 9)), Box::new(one(Stmt::Return(read(t, Ty::I32), 10))));
    let f = with_n(List::Cons(Box::new(Stmt::Local(i, Ty::I32, Expr::Lit(0, Ty::I32), 4)), Box::new(List::Cons(Box::new(lp), Box::new(tail)))));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::NoVar(t, 5));
}

#[test]
fn bool_literals_and_the_largest_uint64_literal_translate() {
    let f = |e: Expr, ret: Ty| Function { ret, ..with_n(one(Stmt::Return(e, 4))) };
    let Model::Full(m) = translate_function(&f(Expr::Bool(true), Ty::Bool), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Bool(true))), 0), Box::new(List::Nil)));
    let Model::Full(m) = translate_function(&f(Expr::Lit(u64::MAX, Ty::U64), Ty::U64), &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(u64::MAX)));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
    // The parser reads the largest literal of a contract.
    assert_eq!(parse_contract(&vec![Tok::Int(u64::MAX)], 3), Ok(Expr::Int(u64::MAX)));
}

#[test]
fn a_contract_reads_a_sequence_by_size_index_forall_and_chain() {
    // forall j :: 0 <= j < v.size() ==> v[j] != 0, over a parameter v of seq<int32>.
    let v = X;
    let j = 70;
    let body = Expr::Bin(
        BinOp::Implies,
        b(Expr::Chain(BinOp::Le, BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(j)), b(Expr::Size(b(Expr::Name(v)))))),
        b(Expr::Bin(BinOp::Ne, b(Expr::Index(b(Expr::Name(v)), b(Expr::Name(j)))), b(Expr::Int(0)))),
    );
    let conds = List::Cons((CondKind::Ensures, Expr::Forall(j, b(body)), 3, names(&[v])), Box::new(List::Nil));
    let f = Function {
        name: SAT,
        line: 4,
        params: List::Cons((v, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false,
        conds,
        body: one(Stmt::Return(Expr::Bool(true), 5)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let len = || Box::new(DExpr::Len(Box::new(DExpr::Var(v))));
    let want = DExpr::Forall(
        j,
        Box::new(DExpr::Bin(
            BinOp::Implies,
            Box::new(DExpr::Chain(BinOp::Le, BinOp::Lt, Box::new(DExpr::Lit(0)), Box::new(DExpr::Bound(j)), len())),
            Box::new(DExpr::Bin(
                BinOp::Ne,
                Box::new(DExpr::AsInt(Box::new(DExpr::Index(Box::new(DExpr::Var(v)), Box::new(DExpr::Bound(j)))))),
                Box::new(DExpr::Lit(0)),
            )),
        )),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // The type Vec holds the bound on the length, so the method requires nothing, decision 0076.
    assert_eq!(m.requires, List::Nil);
}

#[test]
fn code_reads_a_sequence_by_size_and_index() {
    // return v[0] < v.size(); with v of seq<uint8>: the size is (|v| as uint64).
    let v = X;
    let seq = Ty::Seq(Scalar::U8, Extent::Dynamic);
    let idx = Expr::Index(b(Expr::Var(v, seq)), b(Expr::Lit(0, Ty::U64)));
    let size = Expr::Size(b(Expr::Var(v, seq)));
    let e = Expr::Bin(BinOp::Lt, b(Expr::Cast(CastKind::Integral(Ty::U8, Ty::U64), b(Expr::Cast(CastKind::Read, b(idx))))), b(size));
    let f = Function { name: SAT, line: 4, params: List::Cons((v, seq), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, body: one(Stmt::Return(e, 5)) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let didx = DExpr::Index(Box::new(DExpr::Var(v)), Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0)))));
    let dsize = DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(DExpr::Var(v)))));
    let want = DExpr::Bin(BinOp::Lt, Box::new(DExpr::Conv(DTy::UInt64, Box::new(didx))), Box::new(dsize));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
}

#[test]
fn a_sequence_is_in_the_subset_only_as_a_parameter() {
    let seq = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let f = Function { ret: seq, ..with_n(List::Nil) };
    assert_eq!(translate_function(&f, &List::Nil, &List::Nil), Model::Refused(Refusal::SeqParam(3)));
    let local = Stmt::Local(SUM, seq, Expr::Var(X, Ty::I32), 4);
    assert_eq!(bare_refusal(translate_function(&with_n(one(local)), &List::Nil, &List::Nil)), Refusal::SeqParam(4));
}

#[test]
fn a_chain_of_two_directions_and_an_index_of_a_scalar_are_refused() {
    let ens = |e: Expr| List::Cons((CondKind::Ensures, e, 2, names(&[X])), Box::new(List::Nil));
    let mixed = Expr::Chain(BinOp::Lt, BinOp::Gt, b(Expr::Int(0)), b(Expr::Name(X)), b(Expr::Int(1)));
    let f = Function { trusted: false, conds: ens(mixed), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(2));
    let index = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Index(b(Expr::Name(X)), b(Expr::Int(0)))));
    let f = Function { trusted: false, conds: ens(index), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(2));
}

#[test]
fn the_parser_reads_forall_index_size_and_a_chain() {
    // forall j :: 0 <= j < v.size() ==> v[j] != 0
    let (v, j) = (X, 70);
    let toks = vec![
        Tok::Forall, Tok::Ident(j), Tok::ColonColon,
        Tok::Int(0), Tok::Op(BinOp::Le), Tok::Ident(j), Tok::Op(BinOp::Lt), Tok::Ident(v), Tok::Size,
        Tok::Op(BinOp::Implies),
        Tok::Ident(v), Tok::LBracket, Tok::Ident(j), Tok::RBracket, Tok::Op(BinOp::Ne), Tok::Int(0),
    ];
    let want = Expr::Forall(
        j,
        b(Expr::Bin(
            BinOp::Implies,
            b(Expr::Chain(BinOp::Le, BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(j)), b(Expr::Size(b(Expr::Name(v)))))),
            b(Expr::Bin(BinOp::Ne, b(Expr::Index(b(Expr::Name(v)), b(Expr::Name(j)))), b(Expr::Int(0)))),
        )),
    );
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    // An index that does not close is refused.
    assert_eq!(parse_contract(&vec![Tok::Ident(v), Tok::LBracket, Tok::Int(0)], 4), Err(Refusal::Syntax(4)));
}

#[test]
fn each_statement_and_contract_line_keeps_the_place_it_comes_from() {
    // requires lo <= hi at place 21; if (x < lo) at 27 { return lo; at 28 } return x; at 30
    let conds = List::Cons((CondKind::Requires, Expr::Bin(BinOp::Le, b(Expr::Name(LO)), b(Expr::Name(HI))), 21, names(&[X, LO, HI])), Box::new(List::Nil));
    let body = List::Cons(
        Box::new(Stmt::If(Expr::Bin(BinOp::Lt, b(var(X)), b(var(LO))), Box::new(one(Stmt::Return(var(LO), 28))), Box::new(List::Nil), 27)),
        Box::new(one(Stmt::Return(var(X), 30))));
    let f = Function { name: CLAMP, line: 26, params: params(), ret: Ty::I32, trusted: false, conds, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((_, req), _) = m.requires else { panic!("a requires line") };
    assert_eq!(req, 21);
    let List::Cons((first, p1), rest) = m.body else { panic!("a body") };
    let DStmt::If(_, then, _) = *first else { panic!("an if") };
    let List::Cons((_, p2), _) = *then else { panic!("a return") };
    let List::Cons((_, p3), _) = *rest else { panic!("a return") };
    assert_eq!((p1, p2, p3), (27, 28, 30));
    // The length of a span of fixed extent comes from the function's own line.
    let seq = Function { params: List::Cons((X, Ty::Seq(Scalar::I32, Extent::Fixed(3))), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, ..with_n(one(Stmt::Return(Expr::Bool(true), 5))) };
    let Model::Full(m) = translate_function(&seq, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((_, at), _) = m.requires else { panic!("the bound") };
    assert_eq!(at, 3);
}

#[test]
fn a_span_of_fixed_extent_requires_its_length() {
    let f = Function { params: List::Cons((X, Ty::Seq(Scalar::I32, Extent::Fixed(3))), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, ..with_n(one(Stmt::Return(Expr::Bool(true), 5))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(X)))), Box::new(DExpr::Lit(3)));
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_sequence_made_from_a_sequence_keeps_its_value_when_its_length_cannot_change() {
    let dynamic = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let three = Ty::Seq(Scalar::I32, Extent::Fixed(3));
    let copy = |from: Ty, to: Ty| Expr::Cast(CastKind::Construct, b(Expr::Copy(b(Expr::Var(A, from)), from, to)));
    let f = |e: Expr| Function { name: SAT, line: 4, params: List::Cons((A, dynamic), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Local(B, Ty::I32, Expr::Call(SAT, SAT_NAME, Box::new(List::Cons(b(e), Box::new(List::Nil))), 5), 5)) };
    // The callee of each call is the function itself, so each call resolves.
    let all = |e: Expr| fns(vec![f(e)]);
    // A copy, and a span with no fixed extent made from one with a fixed extent, keep the value.
    for (from, to) in [(dynamic, dynamic), (three, dynamic), (three, three)] {
        let m = translate_function(&f(copy(from, to)), &all(copy(from, to)), &List::Nil);
        let Model::Full(m) = m else { panic!("a full model for {from:?} to {to:?}: {m:?}") };
        let List::Cons((s, _), _) = m.body else { panic!("a body") };
        let DStmt::LocalCall(_, _, _, List::Cons(arg, _)) = *s else { panic!("a call") };
        assert_eq!(arg, DExpr::Var(A));
    }
    // A fixed extent made from another length, or another element type, is refused.
    for (from, to) in [(dynamic, three), (Ty::Seq(Scalar::I32, Extent::Fixed(4)), three), (Ty::Seq(Scalar::U8, Extent::Dynamic), dynamic)] {
        let m = translate_function(&f(copy(from, to)), &all(copy(from, to)), &List::Nil);
        assert_eq!(bare_refusal(m), Refusal::Extent(5), "{from:?} to {to:?}");
    }
}

#[test]
fn a_decreases_line_above_a_function_is_the_measure_of_its_recursion() {
    // decreases n, over the parameter of with_n, at place 2.
    let fc = conds(vec![(CondKind::Decreases, Expr::Name(X), 2)]);
    let f = Function { trusted: false, conds: fc, ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    let f = Function { trusted: false, conds: List::Cons((CondKind::Decreases, Expr::Name(X), 2, names(&[X])), Box::new(List::Nil)), ..f };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::AsInt(Box::new(DExpr::Var(X)));
    assert_eq!(m.decreases, List::Cons((want, 2), Box::new(List::Nil)));
    // It names no result.
    let f = Function { trusted: false, conds: List::Cons((CondKind::Decreases, Expr::Result, 2, names(&[X])), Box::new(List::Nil)), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(2));
}

const POINT: u32 = 80;
const FX: u32 = 81;
const FY: u32 = 82;

/// `struct Point { int32_t x; int32_t y; }` as the table of the file.
fn point_table() -> Structs {
    List::Cons((POINT, (4, List::Cons((FX, Ty::I32), Box::new(List::Cons((FY, Ty::I32), Box::new(List::Nil)))), List::Nil)), Box::new(List::Nil))
}

#[test]
fn a_struct_of_scalars_is_a_datatype_with_field_reads_and_braced_values() {
    let pt = Ty::Struct(POINT);
    // Point swap(Point p) { return Point{p.y, p.x}; } with ensures result.x == p.y
    let field = |n: u32, f: u32| Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(n, pt)), f)));
    let args = List::Cons(b(field(A, FY)), Box::new(List::Cons(b(field(A, FX)), Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Field(b(Expr::Result), FX)), b(Expr::Field(b(Expr::Name(A)), FY)));
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, pt), Box::new(List::Nil)),
        ret: pt,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 9, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Construct(POINT, Box::new(args)), 11)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &point_table()) else { panic!("a full model") };
    let dfield = |d: DExpr, f: u32| DExpr::Field(Box::new(d), f);
    let dargs = List::Cons(dfield(DExpr::Var(A), FY), Box::new(List::Cons(dfield(DExpr::Var(A), FX), Box::new(List::Nil))));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Ctor(POINT, Box::new(dargs)))), 0), Box::new(List::Nil)));
    // A field of an integer reads as an exact integer in a contract.
    let as_int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Bin(BinOp::Eq, as_int(dfield(DExpr::Result, FX)), as_int(dfield(DExpr::Var(A), FY)));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    assert_eq!(m.ret, DTy::Struct(POINT));
}

#[test]
fn a_field_the_struct_does_not_have_is_refused() {
    let pt = Ty::Struct(POINT);
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Field(b(Expr::Name(A)), 99)));
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, pt), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 9, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 11)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &point_table())), Refusal::NoField(99, 9));
}

#[test]
fn a_copy_of_a_struct_keeps_its_value_only_as_the_same_struct() {
    assert!(matches!(translate_code(&Expr::Copy(b(Expr::Var(A, Ty::Struct(POINT))), Ty::Struct(POINT), Ty::Struct(POINT)), 3), Ok(DExpr::Var(A))));
    assert_eq!(translate_code(&Expr::Copy(b(Expr::Var(A, Ty::Struct(POINT))), Ty::Struct(POINT), Ty::Struct(7)), 3), Err(Refusal::Extent(3)));
}

#[test]
fn a_struct_has_a_model_when_each_field_is_a_type_of_the_subset() {
    let ok = translate_structs(&point_table());
    assert_eq!(ok, List::Cons(Ok((POINT, List::Cons((FX, DTy::Int32), Box::new(List::Cons((FY, DTy::Int32), Box::new(List::Nil)))))), Box::new(List::Nil)));
    // A field of a type with no rule refuses the struct. A sequence field is in the subset since decision 0076.
    let other_field = List::Cons((POINT, (4, List::Cons((FX, Ty::Other(OTHER_TYPE)), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    assert_eq!(translate_structs(&other_field), List::Cons(Err(Refusal::Construct(OTHER_TYPE, 4)), Box::new(List::Nil)));
}

#[test]
fn the_parser_reads_a_field_after_a_name_or_result() {
    // result.x == p.y, and b.hi.x
    let toks = vec![Tok::Result, Tok::Field(FX), Tok::Op(BinOp::Eq), Tok::Ident(A), Tok::Field(FY)];
    let want = Expr::Bin(BinOp::Eq, b(Expr::Field(b(Expr::Result), FX)), b(Expr::Field(b(Expr::Name(A)), FY)));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    let toks = vec![Tok::Ident(B), Tok::Field(FY), Tok::Field(FX)];
    assert_eq!(parse_contract(&toks, 4), Ok(Expr::Field(b(Expr::Field(b(Expr::Name(B)), FY)), FX)));
}

const SLOT: u32 = 90;
const FV: u32 = 91;

/// `struct Slot { std::optional<int32_t> value; }` as the table of the file.
fn slot_table() -> Structs {
    List::Cons((SLOT, (4, List::Cons((FV, Ty::Opt(Scalar::I32)), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil))
}

#[test]
fn code_reads_an_optional_and_makes_one_from_a_value_or_nullopt() {
    let o = || b(Expr::Var(A, Ty::Opt(Scalar::I32)));
    assert_eq!(translate_code(&Expr::HasValue(o()), 3), Ok(DExpr::IsSome(Box::new(DExpr::Var(A)))));
    assert_eq!(translate_code(&Expr::Value(o()), 3), Ok(DExpr::Get(Box::new(DExpr::Var(A)))));
    assert_eq!(translate_code(&Expr::Nullopt, 3), Ok(DExpr::Nothing));
    assert_eq!(translate_code(&Expr::Wrap(b(var(B))), 3), Ok(DExpr::Just(Box::new(DExpr::Var(B)))));
    assert_eq!(translate_ty(Ty::Opt(Scalar::U8), 3), Ok(DTy::Opt(Scalar::U8)));
    assert_eq!(translate_value_ty(Ty::Opt(Scalar::U8), 3, &List::Nil), Ok(DTy::Opt(Scalar::U8)));
}

#[test]
fn a_contract_reads_an_optional_by_has_value_and_value() {
    let opt = Ty::Opt(Scalar::I32);
    // std::optional<int32_t> nonneg(int32_t x) with ensures result.has_value() ==> result.value() >= 0
    let ens = Expr::Bin(
        BinOp::Implies,
        b(Expr::HasValue(b(Expr::Result))),
        b(Expr::Bin(BinOp::Ge, b(Expr::Value(b(Expr::Result))), b(Expr::Int(0)))),
    );
    // requires s.value.has_value(), on a parameter of the struct Slot
    let req = Expr::HasValue(b(Expr::Field(b(Expr::Name(B)), FV)));
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, Ty::I32), Box::new(List::Cons((B, Ty::Struct(SLOT)), Box::new(List::Nil)))),
        ret: opt,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 8, names(&[A, B])), Box::new(List::Cons((CondKind::Ensures, ens, 9, names(&[A, B])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Nullopt, 11)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &slot_table()) else { panic!("a full model") };
    let want_req = DExpr::IsSome(Box::new(DExpr::Field(Box::new(DExpr::Var(B)), FV)));
    // The value of an integer reads as an exact integer.
    let want_ens = DExpr::Bin(
        BinOp::Implies,
        Box::new(DExpr::IsSome(Box::new(DExpr::Result))),
        Box::new(DExpr::Bin(BinOp::Ge, Box::new(DExpr::AsInt(Box::new(DExpr::Get(Box::new(DExpr::Result))))), Box::new(DExpr::Lit(0)))),
    );
    assert_eq!(strip_conds(m.requires), List::Cons((want_req, 0), Box::new(List::Nil)));
    assert_eq!(strip_conds(m.ensures), List::Cons((want_ens, 0), Box::new(List::Nil)));
    assert_eq!(m.ret, DTy::Opt(Scalar::I32));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Nothing)), 0), Box::new(List::Nil)));
}

#[test]
fn has_value_and_value_of_a_name_that_is_no_optional_are_refused() {
    for e in [Expr::HasValue(b(Expr::Name(A))), Expr::Value(b(Expr::Name(A)))] {
        let f = Function {
            name: SAT,
            line: 10,
            params: List::Cons((A, Ty::I32), Box::new(List::Nil)),
            ret: Ty::Bool,
            trusted: false, conds: List::Cons((CondKind::Requires, e, 9, names(&[A])), Box::new(List::Nil)),
            body: one(Stmt::Return(Expr::Bool(true), 11)),
        };
        assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(9));
    }
}

#[test]
fn a_copy_of_an_optional_keeps_its_value_only_as_the_same_optional() {
    let o = || b(Expr::Var(A, Ty::Opt(Scalar::I32)));
    assert_eq!(translate_code(&Expr::Copy(o(), Ty::Opt(Scalar::I32), Ty::Opt(Scalar::I32)), 3), Ok(DExpr::Var(A)));
    assert_eq!(translate_code(&Expr::Copy(o(), Ty::Opt(Scalar::I32), Ty::Opt(Scalar::I64)), 3), Err(Refusal::Extent(3)));
}

#[test]
fn a_struct_may_hold_an_optional_scalar() {
    let want = List::Cons(Ok((SLOT, List::Cons((FV, DTy::Opt(Scalar::I32)), Box::new(List::Nil)))), Box::new(List::Nil));
    assert_eq!(translate_structs(&slot_table()), want);
}

#[test]
fn the_parser_reads_has_value_and_value_after_a_path() {
    // result.has_value() ==> result.value() >= 0
    let toks = vec![Tok::Result, Tok::HasValue, Tok::Op(BinOp::Implies), Tok::Result, Tok::Value, Tok::Op(BinOp::Ge), Tok::Int(0)];
    let want = Expr::Bin(
        BinOp::Implies,
        b(Expr::HasValue(b(Expr::Result))),
        b(Expr::Bin(BinOp::Ge, b(Expr::Value(b(Expr::Result))), b(Expr::Int(0)))),
    );
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    // s.value.has_value()
    let toks = vec![Tok::Ident(B), Tok::Field(FV), Tok::HasValue];
    assert_eq!(parse_contract(&toks, 4), Ok(Expr::HasValue(b(Expr::Field(b(Expr::Name(B)), FV)))));
}

#[test]
fn a_decreases_line_that_reads_result_through_a_field_or_an_optional_is_refused() {
    // decreases result.x, decreases result.value(), decreases result.has_value()
    // Each result has the type that the read needs, so only the rule on result refuses the line.
    let reads = [
        (Expr::Field(b(Expr::Result), FX), Ty::Struct(POINT), Expr::Construct(POINT, Box::new(List::Cons(b(var(X)), Box::new(List::Cons(b(var(X)), Box::new(List::Nil))))))),
        (Expr::Value(b(Expr::Result)), Ty::Opt(Scalar::I32), Expr::Nullopt),
        (Expr::HasValue(b(Expr::Result)), Ty::Opt(Scalar::I32), Expr::Nullopt),
    ];
    for (e, ret, value) in reads {
        let f = Function { trusted: false, conds: List::Cons((CondKind::Decreases, e, 2, names(&[X])), Box::new(List::Nil)), ret, ..with_n(one(Stmt::Return(value, 4))) };
        assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &point_table())), Refusal::Syntax(2));
    }
}

const NODE: u32 = 100;
const PRE: u32 = 101;
const VAL: u32 = 102;
const CH: u32 = 103;
const WRAP: u32 = 104;
const WN: u32 = 105;

/// `struct Node { std::vector<uint8_t> prefix; std::optional<int32_t> value; std::vector<Node> children; }` and
/// `struct Wrapper { Node n; }` as the table of the file.
fn node_table() -> Structs {
    let node = List::Cons((PRE, Ty::Seq(Scalar::U8, Extent::Dynamic)), Box::new(List::Cons((VAL, Ty::Opt(Scalar::I32)), Box::new(List::Cons((CH, Ty::Seq(Scalar::Struct(NODE), Extent::Dynamic)), Box::new(List::Nil))))));
    let wrap = List::Cons((WN, Ty::Struct(NODE)), Box::new(List::Nil));
    List::Cons((NODE, (7, node, List::Nil)), Box::new(List::Cons((WRAP, (13, wrap, List::Nil)), Box::new(List::Nil))))
}

#[test]
fn a_struct_may_hold_sequences_and_a_sequence_of_itself() {
    let node = List::Cons((PRE, DTy::Seq(Scalar::U8)), Box::new(List::Cons((VAL, DTy::Opt(Scalar::I32)), Box::new(List::Cons((CH, DTy::Seq(Scalar::Struct(NODE))), Box::new(List::Nil))))));
    let wrap = List::Cons((WN, DTy::Struct(NODE)), Box::new(List::Nil));
    let want = List::Cons(Ok((NODE, node)), Box::new(List::Cons(Ok((WRAP, wrap)), Box::new(List::Nil))));
    assert_eq!(translate_structs(&node_table()), want);
}

/// A struct that holds a sequence is a value: a local of Node, a local of Wrapper, which holds a Node by value, and a result of
/// Node translate, decision 0187.
#[test]
fn a_struct_that_holds_a_sequence_is_a_value() {
    let param = |t: Ty| List::Cons((A, t), Box::new(List::Nil));
    for k in [NODE, WRAP] {
        let f = Function {
            name: SAT,
            line: 14,
            params: param(Ty::Struct(k)),
            ret: Ty::I32,
            trusted: false, conds: List::Nil,
            body: List::Cons(
                Box::new(Stmt::Local(B, Ty::Struct(k), read(A, Ty::Struct(k)), 15)),
                Box::new(List::Cons(Box::new(Stmt::Return(Expr::Lit(0, Ty::I32), 16)), Box::new(List::Nil)))),
        };
        let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model of a local") };
        let List::Cons((local, _), _) = strip(m.body) else { panic!("a body") };
        assert_eq!(*local, DStmt::Local(B, DTy::Struct(k), DExpr::Var(A)));
    }
    let result = Function { name: SUCC, line: 19, params: param(Ty::Struct(NODE)), ret: Ty::Struct(NODE), trusted: false, conds: List::Nil, body: one(Stmt::Return(read(A, Ty::Struct(NODE)), 20)) };
    let Model::Full(m) = translate_function(&result, &List::Nil, &node_table()) else { panic!("a full model of a result") };
    assert_eq!(m.ret, DTy::Struct(NODE));
    // An optional of it stays out.
    assert_eq!(translate_value_ty(Ty::Opt(Scalar::Struct(NODE)), 3, &node_table()), Err(Refusal::HoldsSeq(3)));
    assert_eq!(translate_value_ty(Ty::Vec(Scalar::Struct(NODE)), 3, &node_table()), Err(Refusal::HoldsSeq(3)));
}

/// `prefix[i] = e` in a member function of Node that writes its object is a new value of the field. A field that is no sequence, a
/// field that the struct does not have, and a member function that does not write its object are refused, decision 0187.
#[test]
fn a_member_function_writes_one_element_of_a_vector_field() {
    let with = |t: Ty, s: Stmt| Function {
        name: 480,
        line: 9,
        params: List::Cons((THIS, t), Box::new(List::Cons((X, Ty::U64), Box::new(List::Nil)))),
        ret: Ty::Void,
        trusted: false,
        conds: List::Nil,
        body: one(s),
    };
    let write = |f: u32| Stmt::SetFieldAt(f, Expr::Var(X, Ty::U64), Expr::Lit(1, Ty::U8), 10);
    let Model::Full(m) = translate_function(&with(Ty::ThisMut(NODE), write(PRE)), &List::Nil, &node_table()) else { panic!("a full model") };
    let List::Cons((s, _), rest) = strip(m.body) else { panic!("a body") };
    assert_eq!(*rest, List::Nil);
    let DStmt::SetField(f, DExpr::SetAt(base, i, _)) = *s else { panic!("a write of the field: {s:?}") };
    assert_eq!(f, PRE);
    assert_eq!(*base, DExpr::Field(Box::new(DExpr::After), PRE));
    assert_eq!(*i, DExpr::Var(X));
    assert_eq!(bare_refusal(translate_function(&with(Ty::ThisMut(NODE), write(VAL)), &List::Nil, &node_table())), Refusal::Syntax(10));
    assert_eq!(bare_refusal(translate_function(&with(Ty::ThisMut(NODE), write(481)), &List::Nil, &node_table())), Refusal::NoField(481, 10));
    assert_eq!(bare_refusal(translate_function(&with(Ty::This(NODE), write(PRE)), &List::Nil, &node_table())), Refusal::WriteParam(THIS, 10));
}

#[test]
fn a_struct_that_holds_a_sequence_is_a_parameter_by_value_or_by_reference() {
    let f = Function { name: SAT, line: 14, params: List::Cons((A, Ty::Struct(NODE)), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    assert_eq!(m.params, List::Cons((A, DTy::Struct(NODE)), Box::new(List::Nil)));
    assert_eq!(m.requires, List::Nil);
}

#[test]
fn code_reads_a_sequence_on_a_field_and_on_an_element() {
    // n.children[i].prefix[0]
    let node = Ty::Struct(NODE);
    let e = Expr::Index(
        b(Expr::Field(b(Expr::Index(b(Expr::Field(b(Expr::Var(A, node)), CH)), b(read(X, Ty::U64)))), PRE)),
        b(Expr::Lit(0, Ty::U64)),
    );
    let want = DExpr::Index(
        Box::new(DExpr::Field(Box::new(DExpr::Index(Box::new(DExpr::Field(Box::new(DExpr::Var(A)), CH)), Box::new(DExpr::Var(X)))), PRE)),
        Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0)))),
    );
    assert_eq!(translate_code(&e, 3), Ok(want));
}

#[test]
fn a_contract_reads_a_sequence_on_a_path() {
    // forall j :: 0 <= j < n.children.size() ==> n.children[j].prefix.size() > 0, over a parameter n of Node.
    let j = 70;
    let children = || b(Expr::Field(b(Expr::Name(A)), CH));
    let body = Expr::Bin(
        BinOp::Implies,
        b(Expr::Chain(BinOp::Le, BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(j)), b(Expr::Size(children())))),
        b(Expr::Bin(BinOp::Gt, b(Expr::Size(b(Expr::Field(b(Expr::Index(children(), b(Expr::Name(j)))), PRE)))), b(Expr::Int(0)))),
    );
    // and n.prefix[0] == 1, an element of a scalar sequence on a field, read as an exact integer.
    let first = Expr::Bin(BinOp::Eq, b(Expr::Index(b(Expr::Field(b(Expr::Name(A)), PRE)), b(Expr::Int(0)))), b(Expr::Int(1)));
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((A, Ty::Struct(NODE)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, first, 12, names(&[A])), Box::new(List::Cons((CondKind::Ensures, Expr::Forall(j, b(body)), 13, names(&[A])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Bool(true), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    let dchildren = || Box::new(DExpr::Field(Box::new(DExpr::Var(A)), CH));
    let want = DExpr::Forall(
        j,
        Box::new(DExpr::Bin(
            BinOp::Implies,
            Box::new(DExpr::Chain(BinOp::Le, BinOp::Lt, Box::new(DExpr::Lit(0)), Box::new(DExpr::Bound(j)), Box::new(DExpr::Len(dchildren())))),
            Box::new(DExpr::Bin(
                BinOp::Gt,
                Box::new(DExpr::Len(Box::new(DExpr::Field(Box::new(DExpr::Index(dchildren(), Box::new(DExpr::Bound(j)))), PRE)))),
                Box::new(DExpr::Lit(0)),
            )),
        )),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    let want = DExpr::Bin(
        BinOp::Eq,
        Box::new(DExpr::AsInt(Box::new(DExpr::Index(Box::new(DExpr::Field(Box::new(DExpr::Var(A)), PRE)), Box::new(DExpr::Lit(0)))))),
        Box::new(DExpr::Lit(1)),
    );
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_decreases_line_on_a_struct_parameter_is_the_struct_itself() {
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((A, Ty::Struct(NODE)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Decreases, Expr::Name(A), 13, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    assert_eq!(strip_conds(m.decreases), List::Cons((DExpr::Var(A), 0), Box::new(List::Nil)));
}

#[test]
fn the_core_refuses_an_optional_of_a_struct_and_a_sequence_of_bool_by_itself() {
    // Decision 0064 gives a sequence of bool no rule. The core refuses it, so the plugin is not the only guard. Found by the review
    // of decision 0076.
    for t in [Ty::Seq(Scalar::Bool, Extent::Dynamic), Ty::Seq(Scalar::Bool, Extent::Fixed(2))] {
        assert_eq!(translate_ty(t, 7), Err(Refusal::Element(7)));
        assert_eq!(translate_value_ty(t, 7, &node_table()), Err(Refusal::Element(7)));
    }
    // An optional of a struct is in, decision 0137, but not of one that holds a sequence, as a parameter, a local or a result.
    let opt_node = Ty::Opt(Scalar::Struct(NODE));
    assert_eq!(translate_ty(opt_node, 7), Ok(DTy::Opt(Scalar::Struct(NODE))));
    assert_eq!(translate_value_ty(opt_node, 7, &node_table()), Err(Refusal::HoldsSeq(7)));
    assert_eq!(param_ty(opt_node, 7, &node_table()), Err(Refusal::HoldsSeq(7)));
    let point = List::Cons((POINT, (4, List::Cons((FX, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let opt_point = Ty::Opt(Scalar::Struct(POINT));
    assert_eq!(translate_value_ty(opt_point, 7, &point), Ok(DTy::Opt(Scalar::Struct(POINT))));
    assert_eq!(param_ty(opt_point, 7, &point), Ok(DTy::Opt(Scalar::Struct(POINT))));
    // A field that is an optional of a struct has no rule yet, decision 0137.
    let field = List::Cons((POINT, (4, List::Cons((FX, Ty::Opt(Scalar::Struct(POINT))), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    assert_eq!(translate_structs(&field), List::Cons(Err(Refusal::Element(4)), Box::new(List::Nil)));
}

#[test]
fn code_reads_empty_and_takes_a_subspan() {
    let key = || b(Expr::Var(A, Ty::Seq(Scalar::U8, Extent::Dynamic)));
    let len_is_zero = |d: DExpr| DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)));
    assert_eq!(translate_code(&Expr::Empty(key()), 3), Ok(len_is_zero(DExpr::Var(A))));
    // key.subspan(1) is key[1..], and Dafny proves that 1 is at most the length.
    let want = DExpr::Drop(Box::new(DExpr::Var(A)), Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(1)))));
    assert_eq!(translate_code(&Expr::Subspan(key(), b(Expr::Lit(1, Ty::U64))), 3), Ok(want));
    // An unknown offset is refused, never skipped.
    assert_eq!(translate_code(&Expr::Subspan(key(), b(Expr::Unknown(OTHER_TYPE, 4))), 3), Err(Refusal::Construct(OTHER_TYPE, 4)));
}

#[test]
fn a_contract_reads_empty_on_a_path_of_a_sequence() {
    // requires !key.empty(), and n.prefix.empty() on a field
    let req = Expr::Not(b(Expr::Empty(b(Expr::Name(A)))));
    let ens = Expr::Bin(BinOp::Implies, b(Expr::Result), b(Expr::Empty(b(Expr::Field(b(Expr::Name(B)), PRE)))));
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((A, Ty::Seq(Scalar::U8, Extent::Dynamic)), Box::new(List::Cons((B, Ty::Struct(NODE)), Box::new(List::Nil)))),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 12, names(&[A, B])), Box::new(List::Cons((CondKind::Ensures, ens, 13, names(&[A, B])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Bool(true), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    let len_is_zero = |d: DExpr| DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)));
    assert_eq!(strip_conds(m.requires), List::Cons((DExpr::Not(Box::new(len_is_zero(DExpr::Var(A)))), 0), Box::new(List::Nil)));
    let want = DExpr::Bin(BinOp::Implies, Box::new(DExpr::Result), Box::new(len_is_zero(DExpr::Field(Box::new(DExpr::Var(B)), PRE))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn empty_of_a_name_that_is_no_sequence_is_refused() {
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, Ty::I32), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, Expr::Empty(b(Expr::Name(A))), 9, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 11)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(9));
}

#[test]
fn the_parser_reads_empty_after_a_path() {
    // !key.empty() and n.prefix.empty()
    let toks = vec![Tok::Bang, Tok::Ident(A), Tok::Empty];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Not(b(Expr::Empty(b(Expr::Name(A)))))));
    let toks = vec![Tok::Ident(B), Tok::Field(PRE), Tok::Empty];
    assert_eq!(parse_contract(&toks, 4), Ok(Expr::Empty(b(Expr::Field(b(Expr::Name(B)), PRE)))));
}

const MAX: u32 = 110;
const HEIGHT: u32 = 111;

#[test]
fn the_parser_reads_a_call_of_a_specification_function() {
    // Max(a, b) == result, F() and an unclosed call
    let toks = vec![Tok::Ident(MAX), Tok::LParen, Tok::Ident(A), Tok::Comma, Tok::Ident(B), Tok::RParen, Tok::Op(BinOp::Eq), Tok::Result];
    let args = List::Cons(b(Expr::Name(A)), Box::new(List::Cons(b(Expr::Name(B)), Box::new(List::Nil))));
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Bin(BinOp::Eq, b(Expr::Apply(MAX, Box::new(args))), b(Expr::Result))));
    assert_eq!(parse_contract(&vec![Tok::Ident(MAX), Tok::LParen, Tok::RParen], 3), Ok(Expr::Apply(MAX, Box::new(List::Nil))));
    assert_eq!(parse_contract(&vec![Tok::Ident(MAX), Tok::LParen, Tok::Ident(A)], 3), Err(Refusal::Syntax(3)));
    assert_eq!(parse_contract(&vec![Tok::Ident(MAX), Tok::LParen, Tok::Ident(A), Tok::Comma, Tok::RParen], 3), Err(Refusal::Syntax(3)));
}

#[test]
fn a_contract_calls_a_specification_function_with_exact_integers() {
    // ensures result == Max(a, b), and requires Height(n) <= 1000 on a struct parameter
    let ens = Expr::Bin(
        BinOp::Eq,
        b(Expr::Result),
        b(Expr::Apply(MAX, Box::new(List::Cons(b(Expr::Name(A)), Box::new(List::Cons(b(Expr::Name(B)), Box::new(List::Nil))))))),
    );
    let req = Expr::Bin(BinOp::Le, b(Expr::Apply(HEIGHT, Box::new(List::Cons(b(Expr::Name(X)), Box::new(List::Nil))))), b(Expr::Int(1000)));
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((A, Ty::I32), Box::new(List::Cons((B, Ty::I32), Box::new(List::Cons((X, Ty::Struct(NODE)), Box::new(List::Nil)))))),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 12, names(&[A, B, X])), Box::new(List::Cons((CondKind::Ensures, ens, 13, names(&[A, B, X])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    let int = |d: DExpr| DExpr::AsInt(Box::new(d));
    let dargs = List::Cons(int(DExpr::Var(A)), Box::new(List::Cons(int(DExpr::Var(B)), Box::new(List::Nil))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(int(DExpr::Result)), Box::new(DExpr::Apply(MAX, Box::new(dargs))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A struct argument is the datatype value itself.
    let want = DExpr::Bin(BinOp::Le, Box::new(DExpr::Apply(HEIGHT, Box::new(List::Cons(DExpr::Var(X), Box::new(List::Nil))))), Box::new(DExpr::Lit(1000)));
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_specification_function_has_no_place_in_code_or_with_result_in_a_decreases_line() {
    let call = || Expr::Apply(MAX, Box::new(List::Cons(b(var(A)), Box::new(List::Nil))));
    assert_eq!(translate_code(&call(), 3), Err(Refusal::Syntax(3)));
    // decreases Height(result) names the result.
    let dec = Expr::Apply(HEIGHT, Box::new(List::Cons(b(Expr::Result), Box::new(List::Nil))));
    let f = Function { trusted: false, conds: List::Cons((CondKind::Decreases, dec, 2, names(&[X])), Box::new(List::Nil)), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(2));
}

#[test]
fn the_parser_reads_exists_and_several_bound_names() {
    // exists k :: k < a, and forall i, j :: i < j
    let toks = vec![Tok::Exists, Tok::Ident(70), Tok::ColonColon, Tok::Ident(70), Tok::Op(BinOp::Lt), Tok::Ident(A)];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Exists(70, b(Expr::Bin(BinOp::Lt, b(Expr::Name(70)), b(Expr::Name(A)))))));
    let toks = vec![Tok::Forall, Tok::Ident(70), Tok::Comma, Tok::Ident(71), Tok::ColonColon, Tok::Ident(70), Tok::Op(BinOp::Lt), Tok::Ident(71)];
    let want = Expr::Forall(70, b(Expr::Forall(71, b(Expr::Bin(BinOp::Lt, b(Expr::Name(70)), b(Expr::Name(71)))))));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    // A comma with no name after it, and no name at all, are refused.
    assert_eq!(parse_contract(&vec![Tok::Forall, Tok::Ident(70), Tok::Comma, Tok::ColonColon, Tok::Ident(70)], 3), Err(Refusal::Syntax(3)));
    assert_eq!(parse_contract(&vec![Tok::Exists, Tok::ColonColon, Tok::Ident(70)], 3), Err(Refusal::Syntax(3)));
}

#[test]
fn exists_binds_an_exact_integer_in_a_contract() {
    // requires exists k :: 0 <= k < v.size() && v[k] == a, over a sequence parameter v and an integer a
    let k = 70;
    let body = Expr::Bin(
        BinOp::And,
        b(Expr::Chain(BinOp::Le, BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(k)), b(Expr::Size(b(Expr::Name(X)))))),
        b(Expr::Bin(BinOp::Eq, b(Expr::Index(b(Expr::Name(X)), b(Expr::Name(k)))), b(Expr::Name(A)))),
    );
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((X, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Cons((A, Ty::I32), Box::new(List::Nil)))),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, Expr::Exists(k, b(body)), 13, names(&[X, A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Exists(
        k,
        Box::new(DExpr::Bin(
            BinOp::And,
            Box::new(DExpr::Chain(BinOp::Le, BinOp::Lt, Box::new(DExpr::Lit(0)), Box::new(DExpr::Bound(k)), Box::new(DExpr::Len(Box::new(DExpr::Var(X)))))),
            Box::new(DExpr::Bin(BinOp::Eq, int(DExpr::Index(Box::new(DExpr::Var(X)), Box::new(DExpr::Bound(k)))), int(DExpr::Var(A)))),
        )),
    );
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_contract_reads_true_and_false() {
    // result == true || x == false, decision 0084
    let toks = vec![Tok::Result, Tok::Op(BinOp::Eq), Tok::Bool(true), Tok::Op(BinOp::Or), Tok::Ident(X), Tok::Op(BinOp::Eq), Tok::Bool(false)];
    let e = parse_contract(&toks, 3).unwrap();
    let want = Expr::Bin(
        BinOp::Or,
        b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bool(true)))),
        b(Expr::Bin(BinOp::Eq, b(Expr::Name(X)), b(Expr::Bool(false)))),
    );
    assert_eq!(e, want);
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((X, Ty::Bool), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Ensures, e, 9, names(&[X])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 11)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let dwant = DExpr::Bin(
        BinOp::Or,
        Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::Bool(true)))),
        Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Var(X)), Box::new(DExpr::Bool(false)))),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((dwant, 0), Box::new(List::Nil)));
}

#[test]
fn the_body_of_a_quantifier_reaches_to_the_end_of_the_line() {
    // forall i :: 0 <= i < a < b holds the whole chain, decision 0131. Before 0131 the body stopped after three operands, and the
    // line was refused, so the rest never fell outside the forall.
    let toks = vec![
        Tok::Forall, Tok::Ident(70), Tok::ColonColon, Tok::Int(0), Tok::Op(BinOp::Le), Tok::Ident(70), Tok::Op(BinOp::Lt), Tok::Ident(A),
        Tok::Op(BinOp::Lt), Tok::Ident(B),
    ];
    let chain = |o1, x: Expr, y: Expr, z: Expr| Expr::Chain(o1, BinOp::Lt, b(x), b(y), b(z));
    let body = Expr::Bin(BinOp::And, b(chain(BinOp::Le, Expr::Int(0), Expr::Name(70), Expr::Name(A))), b(chain(BinOp::Lt, Expr::Name(70), Expr::Name(A), Expr::Name(B))));
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Forall(70, b(body))));
    // In parentheses, the body ends at the bracket, and the line goes on.
    let toks = vec![
        Tok::LParen, Tok::Forall, Tok::Ident(70), Tok::ColonColon, Tok::Ident(70), Tok::Op(BinOp::Lt), Tok::Ident(A), Tok::RParen,
        Tok::Op(BinOp::And), Tok::Ident(B),
    ];
    let want = Expr::Bin(BinOp::And, b(Expr::Forall(70, b(Expr::Bin(BinOp::Lt, b(Expr::Name(70)), b(Expr::Name(A)))))), b(Expr::Name(B)));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
}

const COUNT: u32 = 120;

#[test]
fn the_parser_reads_the_three_slices() {
    // v[i..], v[..j], v[i..j] and v[1..3][0]
    let suffix = vec![Tok::Ident(X), Tok::LBracket, Tok::Ident(A), Tok::DotDot, Tok::RBracket];
    assert_eq!(parse_contract(&suffix, 3), Ok(Expr::Suffix(b(Expr::Name(X)), b(Expr::Name(A)))));
    let prefix = vec![Tok::Ident(X), Tok::LBracket, Tok::DotDot, Tok::Ident(B), Tok::RBracket];
    assert_eq!(parse_contract(&prefix, 3), Ok(Expr::Prefix(b(Expr::Name(X)), b(Expr::Name(B)))));
    let slice = vec![Tok::Ident(X), Tok::LBracket, Tok::Ident(A), Tok::DotDot, Tok::Ident(B), Tok::RBracket];
    assert_eq!(parse_contract(&slice, 3), Ok(Expr::Slice(b(Expr::Name(X)), b(Expr::Name(A)), b(Expr::Name(B)))));
    let element = vec![Tok::Ident(X), Tok::LBracket, Tok::Int(1), Tok::DotDot, Tok::Int(3), Tok::RBracket, Tok::LBracket, Tok::Int(0), Tok::RBracket];
    assert_eq!(parse_contract(&element, 3), Ok(Expr::Index(b(Expr::Slice(b(Expr::Name(X)), b(Expr::Int(1)), b(Expr::Int(3)))), b(Expr::Int(0)))));
    // [..] alone, and a slice with no closing bracket, are refused.
    assert_eq!(parse_contract(&vec![Tok::Ident(X), Tok::LBracket, Tok::DotDot, Tok::RBracket], 3), Err(Refusal::Syntax(3)));
    assert_eq!(parse_contract(&vec![Tok::Ident(X), Tok::LBracket, Tok::Ident(A), Tok::DotDot], 3), Err(Refusal::Syntax(3)));
}

#[test]
fn a_contract_reads_a_part_of_a_sequence_and_passes_it_to_a_function() {
    // ensures result == Count(v[i..], x), and v[..2][1] == 1 on a sequence parameter v
    let call = Expr::Apply(COUNT, Box::new(List::Cons(b(Expr::Suffix(b(Expr::Name(X)), b(Expr::Name(A)))), Box::new(List::Cons(b(Expr::Name(B)), Box::new(List::Nil))))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(call));
    let req = Expr::Bin(BinOp::Eq, b(Expr::Index(b(Expr::Prefix(b(Expr::Name(X)), b(Expr::Int(2)))), b(Expr::Int(1)))), b(Expr::Int(1)));
    let f = Function {
        name: SAT,
        line: 14,
        params: List::Cons((X, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Cons((A, Ty::U64), Box::new(List::Cons((B, Ty::I32), Box::new(List::Nil)))))),
        ret: Ty::U64,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 12, names(&[X, A, B])), Box::new(List::Cons((CondKind::Ensures, ens, 13, names(&[X, A, B])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Lit(0, Ty::U64), 15)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let int = |d: DExpr| DExpr::AsInt(Box::new(d));
    // A part is a sequence, so it passes as itself. Its bound reads as an exact integer.
    let dargs = List::Cons(DExpr::Drop(Box::new(DExpr::Var(X)), Box::new(int(DExpr::Var(A)))), Box::new(List::Cons(int(DExpr::Var(B)), Box::new(List::Nil))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(int(DExpr::Result)), Box::new(DExpr::Apply(COUNT, Box::new(dargs))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    let want = DExpr::Bin(
        BinOp::Eq,
        Box::new(int(DExpr::Index(Box::new(DExpr::Take(Box::new(DExpr::Var(X)), Box::new(DExpr::Lit(2)))), Box::new(DExpr::Lit(1))))),
        Box::new(DExpr::Lit(1)),
    );
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_slice_of_a_name_that_is_no_sequence_and_a_slice_in_code_are_refused() {
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, Ty::I32), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, Expr::Bin(BinOp::Eq, b(Expr::Size(b(Expr::Suffix(b(Expr::Name(A)), b(Expr::Int(1)))))), b(Expr::Int(0))), 9, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 11)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(9));
    let seq = || b(Expr::Var(X, Ty::Seq(Scalar::I32, Extent::Dynamic)));
    assert_eq!(translate_code(&Expr::Suffix(seq(), b(Expr::Lit(1, Ty::U64))), 3), Err(Refusal::Syntax(3)));
}

#[test]
fn code_divides_and_takes_the_remainder_as_cpp_does() {
    // a / 2 and a % 2 on int32_t, with the type of the result that the compiler gave
    let two = || b(Expr::Lit(2, Ty::I32));
    let int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let lit2 = || DExpr::Conv(DTy::Int32, Box::new(DExpr::Lit(2)));
    let div = Expr::Divide(BinOp::Div, b(read(A, Ty::I32)), two(), Ty::I32);
    assert_eq!(translate_code(&div, 3), Ok(DExpr::DivIn(int(DExpr::Var(A)), int(lit2()), DTy::Int32)));
    let rem = Expr::Divide(BinOp::Rem, b(read(A, Ty::I32)), two(), Ty::I32);
    assert_eq!(translate_code(&rem, 3), Ok(DExpr::RemIn(int(DExpr::Var(A)), int(lit2()), DTy::Int32)));
    // A division with no type, as a plain binary node, and a division of bool, are refused.
    assert_eq!(translate_code(&Expr::Bin(BinOp::Div, b(var(A)), b(var(B))), 3), Err(Refusal::Syntax(3)));
    assert_eq!(translate_code(&Expr::Divide(BinOp::Div, b(Expr::Bool(true)), b(Expr::Bool(true)), Ty::Bool), 3), Err(Refusal::Convert(3)));
    assert_eq!(translate_code(&Expr::Divide(BinOp::Add, b(var(A)), b(var(B)), Ty::I32), 3), Err(Refusal::Syntax(3)));
}

#[test]
fn a_contract_divides_with_trunc_div_and_trunc_rem() {
    // ensures result == a / b && result % 2 == 0
    let ens = Expr::Bin(
        BinOp::And,
        b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Div, b(Expr::Name(A)), b(Expr::Name(B)))))),
        b(Expr::Bin(BinOp::Eq, b(Expr::Bin(BinOp::Rem, b(Expr::Result), b(Expr::Int(2)))), b(Expr::Int(0)))),
    );
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, Ty::I32), Box::new(List::Cons((B, Ty::I32), Box::new(List::Nil)))),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 9, names(&[A, B])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 11)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Bin(
        BinOp::And,
        Box::new(DExpr::Bin(BinOp::Eq, int(DExpr::Result), Box::new(DExpr::TDiv(int(DExpr::Var(A)), int(DExpr::Var(B)))))),
        Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::TRem(int(DExpr::Result), Box::new(DExpr::Lit(2)))), Box::new(DExpr::Lit(0)))),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn the_parser_reads_division_and_remainder_with_multiplication() {
    // a / b % c is (a / b) % c, and a + b / c is a + (b / c)
    let toks = vec![Tok::Ident(A), Tok::Op(BinOp::Div), Tok::Ident(B), Tok::Op(BinOp::Rem), Tok::Ident(X)];
    let want = Expr::Bin(BinOp::Rem, b(Expr::Bin(BinOp::Div, b(Expr::Name(A)), b(Expr::Name(B)))), b(Expr::Name(X)));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    let toks = vec![Tok::Ident(A), Tok::Op(BinOp::Add), Tok::Ident(B), Tok::Op(BinOp::Div), Tok::Ident(X)];
    let want = Expr::Bin(BinOp::Add, b(Expr::Name(A)), b(Expr::Bin(BinOp::Div, b(Expr::Name(B)), b(Expr::Name(X)))));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
}

const THIS: u32 = 130;
const CN: u32 = 131;
const COUNTER: u32 = 132;

/// `struct Counter { int32_t n_; }` as the table of the file. The names of a member function's declaration start with this, as its
/// parameters do, so a contract reads each parameter by its place, decision 0060.
fn counter_table() -> Structs {
    List::Cons((COUNTER, (4, List::Cons((CN, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil))
}

#[test]
fn a_const_member_function_reads_its_object_as_the_parameter_this() {
    // int32_t Counter::next() const with requires n_ < 1000, ensures result == n_ + 1, return n_ + 1
    let this = List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil));
    let req = Expr::Bin(BinOp::Lt, b(Expr::Name(CN)), b(Expr::Int(1000)));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Add, b(Expr::Name(CN)), b(Expr::Int(1)))));
    let field = Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let f = Function {
        name: SAT,
        line: 9,
        params: this,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 7, names(&[THIS])), Box::new(List::Cons((CondKind::Ensures, ens, 8, names(&[THIS])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Bin(BinOp::Add, b(field), b(Expr::Lit(1, Ty::I32))), 10)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &counter_table()) else { panic!("a full model") };
    // The object is a value of the datatype.
    assert_eq!(m.params, List::Cons((THIS, DTy::Struct(COUNTER)), Box::new(List::Nil)));
    // A bare field name in a contract is the field of this, read as an exact integer.
    let n = || Box::new(DExpr::AsInt(Box::new(DExpr::Field(Box::new(DExpr::Var(THIS)), CN))));
    assert_eq!(strip_conds(m.requires), List::Cons((DExpr::Bin(BinOp::Lt, n(), Box::new(DExpr::Lit(1000))), 0), Box::new(List::Nil)));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::Bin(BinOp::Add, n(), Box::new(DExpr::Lit(1)))));
    // The body is one return with no call, so the function is pure and its method also gives the value of its function, decision 0090.
    let link = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(SAT, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Cons((link, 0), Box::new(List::Nil)))));
    let body = DExpr::Bin(BinOp::Add, Box::new(DExpr::Field(Box::new(DExpr::Var(THIS)), CN)), Box::new(lit32(1)));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(body)), 0), Box::new(List::Nil)));
}

#[test]
fn a_parameter_wins_over_a_field_and_a_name_that_is_neither_is_refused() {
    // int32_t Counter::shadow(int32_t n_) const with ensures result == n_: the parameter, as in C++
    let ps = List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Cons((CN, Ty::I32), Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(CN)));
    let f = Function {
        name: SAT,
        line: 9,
        params: ps,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 8, names(&[THIS, CN])), Box::new(List::Nil)),
        body: one(Stmt::Return(read(CN, Ty::I32), 10)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &counter_table()) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::AsInt(Box::new(DExpr::Var(CN)))));
    let args = List::Cons(DExpr::Var(THIS), Box::new(List::Cons(DExpr::Var(CN), Box::new(List::Nil))));
    let link = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(SAT, Box::new(args))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Cons((link, 0), Box::new(List::Nil)))));
    // ensures result == m_, where m_ is no parameter and no field of Counter
    let f = Function {
        name: SAT,
        line: 9,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(99))), 8, names(&[THIS])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 10)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &counter_table())), Refusal::Name(99, 8));
    // A free function has no this, so a field name alone is no parameter there.
    let f = Function {
        name: SAT,
        line: 9,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(CN))), 8, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 10)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &counter_table())), Refusal::Name(CN, 8));
}

#[test]
fn the_object_is_a_parameter_and_no_local_or_result() {
    assert_eq!(translate_ty(Ty::This(COUNTER), 3), Ok(DTy::Struct(COUNTER)));
    assert_eq!(translate_value_ty(Ty::This(COUNTER), 3, &counter_table()), Err(Refusal::Syntax(3)));
}

const VALID: u32 = 140;
const VALUE: u32 = 141;
const VKEY: u32 = 142;
const NKEY: u32 = 143;

/// Counter with its members valid and value. `Some(t)` marks a pure member that gives a `t`, with this as its only parameter.
fn members_table(valid: Option<Ty>, value: Option<Ty>) -> Structs {
    let pure = |t: Option<Ty>| t.map(|t| (t, List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil))));
    let ms = List::Cons((VALID, (VKEY, pure(valid))), Box::new(List::Cons((VALUE, (NKEY, pure(value))), Box::new(List::Nil))));
    List::Cons((COUNTER, (4, List::Cons((CN, Ty::I32), Box::new(List::Nil)), ms)), Box::new(List::Nil))
}

/// `int32_t Counter::value() const { return n_; }` with the key NKEY, or with another body.
fn value_fn(body: Stmts) -> Function {
    Function { name: NKEY, line: 9, params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body }
}

#[test]
fn a_pure_member_function_is_also_a_function_and_its_method_gives_its_value() {
    let field = Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let Model::Full(m) = translate_function(&value_fn(one(Stmt::Return(field, 10))), &List::Nil, &members_table(None, None)) else { panic!("a full model") };
    let dfield = DExpr::Field(Box::new(DExpr::Var(THIS)), CN);
    assert_eq!(m.function, Some(dfield));
    // The method gains ensures result == F(this), at the line of the function.
    let link = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(NKEY, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))))));
    assert_eq!(m.ensures, List::Cons((link, 9), Box::new(List::Nil)));
}

#[test]
fn a_member_function_that_writes_a_local_is_not_pure_and_a_free_function_is_pure_only_when_the_file_lists_it() {
    // A local alone keeps the body pure, decision 0172. A write to it does not.
    let field = || Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let write = Box::new(List::Cons(Box::new(Stmt::Assign(A, field(), 11)), Box::new(one(Stmt::Return(read(A, Ty::I32), 12)))));
    let body = List::Cons(Box::new(Stmt::Local(A, Ty::I32, field(), 10)), write);
    let Model::Full(m) = translate_function(&value_fn(body), &List::Nil, &members_table(None, None)) else { panic!("a full model") };
    assert_eq!(m.function, None);
    assert_eq!(m.ensures, List::Nil);
    let free = Function { name: SAT, line: 3, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(read(X, Ty::I32), 4)) };
    let Model::Full(m) = translate_function(&free, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.function, None);
    // The file lists it, so it has a twin, decision 0176.
    let listed = List::Cons((SAT, (SATKEY, Some((Ty::I32, List::Cons((X, Ty::I32), Box::new(List::Nil)))))), Box::new(List::Nil));
    let table: Structs = List::Cons((FILE_ENTRY, (0, List::Nil, listed)), Box::new(List::Nil));
    let Model::Full(m) = translate_function(&Function { name: SATKEY, ..free }, &List::Nil, &table) else { panic!("a full model") };
    assert_eq!(m.function, Some(DExpr::Var(X)));
}

#[test]
fn a_contract_calls_a_pure_member_function_on_this_or_on_a_path() {
    // In a member function: requires valid(). In a free function of c: ensures result == c.value().
    let table = members_table(Some(Ty::Bool), Some(Ty::I32));
    let req = Expr::Apply(VALID, Box::new(List::Nil));
    let f = Function {
        name: SAT,
        line: 9,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 8, names(&[THIS])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 10)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let on_this = DExpr::FCall(VKEY, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))));
    assert_eq!(strip_conds(m.requires), List::Cons((on_this, 0), Box::new(List::Nil)));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Name(A)), VALUE, Box::new(List::Nil))));
    let g = Function {
        name: SAT,
        line: 20,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 19, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
    };
    let Model::Full(m) = translate_function(&g, &List::Nil, &table) else { panic!("a full model") };
    // The value of an integer function reads as an exact integer.
    let call = DExpr::AsInt(Box::new(DExpr::FCall(NKEY, Box::new(List::Cons(DExpr::Var(A), Box::new(List::Nil))))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(call));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

/// A call of a plain member function, one return of an expression with no call, is its function in place. A call of a member
/// function with more than one statement runs before its statement, decision 0189.
#[test]
fn a_call_of_a_plain_member_function_is_its_function_in_place() {
    let read_n = || Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let caller = || Function {
        name: SAT,
        line: 20,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Nil,
        body: one(Stmt::Return(Expr::Bin(BinOp::Add, b(call(NKEY, vec![read(A, Ty::Struct(COUNTER))], 21)), b(Expr::Lit(1, Ty::I32))), 21)),
    };
    let plain = value_fn(one(Stmt::Return(read_n(), 10)));
    let List::Cons(_, rest) = translate_unit(&fns(vec![plain, caller()]), &members_table(None, None)) else { panic!("models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the caller") };
    let List::Cons((s, _), rest) = strip(m.body) else { panic!("a body") };
    assert_eq!(*rest, List::Nil);
    let DStmt::Return(DExpr::Bin(BinOp::Add, l, r)) = *s else { panic!("a return of a sum: {s:?}") };
    assert_eq!(*l, DExpr::FCall(NKEY, Box::new(List::Cons(DExpr::Var(A), Box::new(List::Nil)))));
    assert_eq!(*r, lit32(1));
    // Two statements: the call runs before its statement.
    let two = value_fn(List::Cons(Box::new(Stmt::Local(B, Ty::I32, read_n(), 10)), Box::new(one(Stmt::Return(read(B, Ty::I32), 11)))));
    let List::Cons(_, rest) = translate_unit(&fns(vec![two, caller()]), &members_table(None, None)) else { panic!("models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the caller") };
    let List::Cons((s, _), _) = strip(m.body) else { panic!("a body") };
    assert!(matches!(&*s, DStmt::Pre(_, _)), "{s:?}");
}

#[test]
fn a_contract_that_calls_a_member_function_that_is_not_pure_is_refused() {
    // value is a member that is not pure, and three is no member.
    let table = members_table(Some(Ty::Bool), None);
    for name in [VALUE, 99] {
        let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Name(A)), name, Box::new(List::Nil))));
        let g = Function {
            name: SAT,
            line: 20,
            params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
            ret: Ty::I32,
            trusted: false, conds: List::Cons((CondKind::Ensures, ens, 19, names(&[A])), Box::new(List::Nil)),
            body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
        };
        assert_eq!(bare_refusal(translate_function(&g, &List::Nil, &table)), Refusal::NotPure(name, 19));
    }
}

#[test]
fn the_unit_marks_which_members_are_pure_whatever_the_table_says() {
    // The table claims that value is pure and valid is not. The unit computes it: value is pure, and valid, here a member that
    // writes a local, is not. So a contract that calls valid() is refused, and one that calls c.value() reads the function.
    let field = || Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let value = value_fn(one(Stmt::Return(field(), 10)));
    let valid = Function {
        name: VKEY,
        line: 12,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(B, Ty::Bool, Expr::Bool(true), 13)),
            Box::new(List::Cons(Box::new(Stmt::Assign(B, Expr::Bool(true), 14)), Box::new(one(Stmt::Return(read(B, Ty::Bool), 15))))),
        ),
    };
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Name(A)), VALUE, Box::new(List::Nil))));
    let user = Function {
        name: SAT,
        line: 20,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 19, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
    };
    let bad = Function {
        trusted: false, conds: List::Cons((CondKind::Ensures, Expr::MApply(b(Expr::Name(A)), VALID, Box::new(List::Nil)), 23, names(&[A])), Box::new(List::Nil)),
        line: 24,
        ret: Ty::Bool,
        body: one(Stmt::Return(Expr::Bool(true), 25)),
        ..Function { name: SUCC, line: 24, params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, body: List::Nil }
    };
    let claimed = members_table(Some(Ty::Bool), None);
    let List::Cons(_, rest) = translate_unit(&fns(vec![value, valid, user, bad]), &claimed) else { panic!("models") };
    let List::Cons(_, rest) = *rest else { panic!("models") };
    let List::Cons(Model::Full(m), rest) = *rest else { panic!("a full model of user") };
    let call = DExpr::AsInt(Box::new(DExpr::FCall(NKEY, Box::new(List::Cons(DExpr::Var(A), Box::new(List::Nil))))));
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(call)), 0), Box::new(List::Nil)));
    let List::Cons(last, _) = *rest else { panic!("models") };
    assert_eq!(bare_refusal(last), Refusal::NotPure(VALID, 23));
}

/// A contract that calls a member with no function of the file, as a member of a class template that no instance makes, gets the
/// sentence of a call with no model by the key of the member. A member that is not pure keeps its own sentence, decision 0188.
#[test]
fn a_contract_call_of_a_member_with_no_function_has_no_model() {
    let user = Function {
        name: SAT,
        line: 24,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false,
        conds: List::Cons((CondKind::Requires, Expr::MApply(b(Expr::Name(A)), VALID, Box::new(List::Nil)), 23, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 25)),
    };
    let List::Cons(m, _) = translate_unit(&fns(vec![user]), &members_table(None, None)) else { panic!("a model") };
    assert_eq!(bare_refusal(m), Refusal::Callee(VKEY, 23));
}

#[test]
fn the_parser_reads_a_call_of_a_member_function_on_a_path() {
    // c.value() and c.get(1, b)
    let toks = vec![Tok::Ident(A), Tok::Field(VALUE), Tok::LParen, Tok::RParen];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::MApply(b(Expr::Name(A)), VALUE, Box::new(List::Nil))));
    let toks = vec![Tok::Ident(A), Tok::Field(VALUE), Tok::LParen, Tok::Int(1), Tok::Comma, Tok::Ident(B), Tok::RParen];
    let args = List::Cons(b(Expr::Int(1)), Box::new(List::Cons(b(Expr::Name(B)), Box::new(List::Nil))));
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::MApply(b(Expr::Name(A)), VALUE, Box::new(args))));
    // A field with no call stays a field.
    assert_eq!(parse_contract(&vec![Tok::Ident(A), Tok::Field(VALUE)], 3), Ok(Expr::Field(b(Expr::Name(A)), VALUE)));
}

const LE: u32 = 160;
const LEKEY: u32 = 161;

#[test]
fn an_integer_argument_of_a_member_function_passes_as_the_type_of_its_parameter() {
    // bool Counter::le(int32_t k) const, called as c.le(x) in a contract, with x an int32_t parameter
    let le = List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Cons((X, Ty::I32), Box::new(List::Nil))));
    let ms = List::Cons((LE, (LEKEY, Some((Ty::Bool, le)))), Box::new(List::Nil));
    let table = List::Cons((COUNTER, (4, List::Cons((CN, Ty::I32), Box::new(List::Nil)), ms)), Box::new(List::Nil));
    let req = Expr::MApply(b(Expr::Name(A)), LE, Box::new(List::Cons(b(Expr::Name(B)), Box::new(List::Nil))));
    let f = Function {
        name: SAT,
        line: 20,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Cons((B, Ty::I32), Box::new(List::Nil)))),
        ret: Ty::Bool,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 19, names(&[A, B])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 21)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let arg = DExpr::Conv(DTy::Int32, Box::new(DExpr::AsInt(Box::new(DExpr::Var(B)))));
    let want = DExpr::FCall(LEKEY, Box::new(List::Cons(DExpr::Var(A), Box::new(List::Cons(arg, Box::new(List::Nil))))));
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_member_function_whose_contract_is_refused_is_not_pure() {
    // value has one return, but its requires line names nothing. So value is not pure, and a contract that calls it is refused.
    let field = Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let value = Function {
        trusted: false, conds: List::Cons((CondKind::Requires, Expr::Name(99), 8, names(&[THIS])), Box::new(List::Nil)),
        ..value_fn(one(Stmt::Return(field, 10)))
    };
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Name(A)), VALUE, Box::new(List::Nil))));
    let user = Function {
        name: SAT,
        line: 20,
        params: List::Cons((A, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 19, names(&[A])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
    };
    let List::Cons(first, rest) = translate_unit(&fns(vec![value, user]), &members_table(None, Some(Ty::I32))) else { panic!("models") };
    assert_eq!(bare_refusal(first), Refusal::Name(99, 8));
    let List::Cons(second, _) = *rest else { panic!("models") };
    assert_eq!(bare_refusal(second), Refusal::NotPure(VALUE, 19));
}

const CTOR: u32 = 150;

#[test]
fn a_constructor_gives_the_value_it_builds_and_its_contract_reads_that_value() {
    // explicit Counter(int32_t n) : n_(n) {} with requires n < 1000 and ensures valid() && n_ == n
    let table = members_table(Some(Ty::Bool), None);
    let req = Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Int(1000)));
    let ens = Expr::Bin(BinOp::And, b(Expr::Apply(VALID, Box::new(List::Nil))), b(Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Name(X)))));
    let f = Function {
        name: CTOR,
        line: 9,
        params: List::Cons((X, Ty::I32), Box::new(List::Nil)),
        ret: Ty::This(COUNTER),
        trusted: false, conds: List::Cons((CondKind::Requires, req, 7, names(&[X])), Box::new(List::Cons((CondKind::Ensures, ens, 8, names(&[X])), Box::new(List::Nil)))),
        body: one(Stmt::Return(Expr::Construct(COUNTER, Box::new(List::Cons(b(read(X, Ty::I32)), Box::new(List::Nil)))), 9)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    // The result is a value of the datatype.
    assert_eq!(m.ret, DTy::Struct(COUNTER));
    // valid() passes result, and n_ is the field of result.
    let valid = DExpr::FCall(VKEY, Box::new(List::Cons(DExpr::Result, Box::new(List::Nil))));
    let n = DExpr::AsInt(Box::new(DExpr::Field(Box::new(DExpr::Result), CN)));
    let want = DExpr::Bin(BinOp::And, Box::new(valid), Box::new(DExpr::Bin(BinOp::Eq, Box::new(n), Box::new(DExpr::AsInt(Box::new(DExpr::Var(X)))))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A constructor has no this, so it is no pure member function.
    assert_eq!(m.function, None);
}

/// A constructor of a struct that holds a sequence gives its value, decision 0187.
#[test]
fn a_constructor_of_a_struct_that_holds_a_sequence_gives_its_value() {
    let f = Function {
        name: CTOR,
        line: 9,
        params: List::Cons((A, Ty::Struct(NODE)), Box::new(List::Nil)),
        ret: Ty::This(NODE),
        trusted: false, conds: List::Nil,
        body: one(Stmt::Return(read(A, Ty::Struct(NODE)), 9)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &node_table()) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Struct(NODE));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Var(A))), 0), Box::new(List::Nil)));
}

const BUMP: u32 = 170;
const TAKE: u32 = 171;
const LOC: u32 = 172;

/// `void Counter::bump()` with requires n_ < 1000 and ensures n_ == old(n_) + 1, and a body of n_ = n_ + 1.
fn bump_fn() -> Function {
    let this = List::Cons((THIS, Ty::ThisMut(COUNTER)), Box::new(List::Nil));
    let req = Expr::Bin(BinOp::Lt, b(Expr::Name(CN)), b(Expr::Int(1000)));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Bin(BinOp::Add, b(Expr::Old(b(Expr::Name(CN)))), b(Expr::Int(1)))));
    let field = Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::ThisMut(COUNTER))), CN)));
    Function {
        name: BUMP,
        line: 9,
        params: this,
        ret: Ty::Void,
        trusted: false, conds: List::Cons((CondKind::Requires, req, 7, names(&[THIS])), Box::new(List::Cons((CondKind::Ensures, ens, 8, names(&[THIS])), Box::new(List::Nil)))),
        body: one(Stmt::SetField(CN, Expr::Bin(BinOp::Add, b(field), b(Expr::Lit(1, Ty::I32))), 10)),
    }
}

#[test]
fn a_member_function_that_writes_its_object_gives_it_back() {
    let Model::Full(m) = translate_function(&bump_fn(), &List::Nil, &counter_table()) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Void);
    assert!(m.writes);
    // The body reads and writes the object after: this'.
    let after = || Box::new(DExpr::Field(Box::new(DExpr::After), CN));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::SetField(CN, DExpr::Bin(BinOp::Add, after(), Box::new(lit32(1))))), 0), Box::new(List::Nil)));
    // A requires line reads the object before the call. An ensures line reads it after, and old() before.
    let before = || Box::new(DExpr::AsInt(Box::new(DExpr::Field(Box::new(DExpr::Var(THIS)), CN))));
    assert_eq!(strip_conds(m.requires), List::Cons((DExpr::Bin(BinOp::Lt, before(), Box::new(DExpr::Lit(1000))), 0), Box::new(List::Nil)));
    let want = DExpr::Bin(
        BinOp::Eq,
        Box::new(DExpr::AsInt(Box::new(DExpr::Field(Box::new(DExpr::After), CN)))),
        Box::new(DExpr::Bin(BinOp::Add, before(), Box::new(DExpr::Lit(1)))),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_const_member_function_writes_no_field_and_old_reads_only_in_an_ensures_line() {
    // A field write in a const member function writes a parameter.
    let f = Function { params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)), trusted: false, conds: List::Nil, ..bump_fn() };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &counter_table())), Refusal::WriteParam(THIS, 10));
    // old() in a requires line of a function that writes its object, and in a free function.
    let old = Expr::Bin(BinOp::Lt, b(Expr::Old(b(Expr::Name(CN)))), b(Expr::Int(1000)));
    let f = Function { trusted: false, conds: List::Cons((CondKind::Requires, old, 7, names(&[THIS])), Box::new(List::Nil)), ..bump_fn() };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &counter_table())), Refusal::Syntax(7));
    let free = Function {
        trusted: false, conds: List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Old(b(Expr::Name(X))))), 2, names(&[X])), Box::new(List::Nil)),
        ..with_n(one(Stmt::Return(read(X, Ty::I32), 4)))
    };
    assert_eq!(bare_refusal(translate_function(&free, &List::Nil, &counter_table())), Refusal::Syntax(2));
}

#[test]
fn a_call_that_writes_its_object_writes_a_local_back() {
    // Counter c{5}; c.bump(); int32_t r = c.take(); return r;
    let take = Function {
        name: TAKE,
        line: 20,
        params: List::Cons((THIS, Ty::ThisMut(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false, conds: List::Nil,
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
    };
    let obj = || Box::new(List::Cons(b(read(LOC, Ty::Struct(COUNTER))), Box::new(List::Nil)));
    let all = fns(vec![bump_fn(), take]);
    let user = Function {
        name: SAT,
        line: 29,
        params: List::Nil,
        ret: Ty::I32,
        trusted: false, conds: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(LOC, Ty::Struct(COUNTER), Expr::Construct(COUNTER, Box::new(List::Cons(b(Expr::Lit(5, Ty::I32)), Box::new(List::Nil)))), 30)),
            Box::new(List::Cons(
                Box::new(Stmt::Call(BUMP, SAT_NAME, obj(), 31)),
                Box::new(List::Cons(
                    Box::new(Stmt::Local(A, Ty::I32, Expr::Call(TAKE, SAT_NAME, obj(), 32), 32)),
                    Box::new(one(Stmt::Return(read(A, Ty::I32), 33)))))))),
    };
    let Model::Full(m) = translate_function(&user, &all, &counter_table()) else { panic!("a full model") };
    let List::Cons((_, _), rest) = strip(m.body) else { panic!("a body") };
    let List::Cons((update, _), rest) = *rest else { panic!("an update") };
    assert_eq!(*update, DStmt::Update(objs(&[Obj::Local(LOC)]), BUMP, dargs(vec![DExpr::Var(LOC)])));
    let List::Cons((local, _), _) = *rest else { panic!("a local") };
    assert_eq!(*local, DStmt::LocalUpdate(A, DTy::Int32, objs(&[Obj::Local(LOC)]), TAKE, dargs(vec![DExpr::Var(LOC)])));
}

#[test]
fn a_call_that_writes_a_parameter_or_a_field_is_refused() {
    let all = fns(vec![bump_fn()]);
    // void f(Counter c) { c.bump(); }
    let on_param = Function {
        name: SAT,
        line: 16,
        params: List::Cons((LOC, Ty::Struct(COUNTER)), Box::new(List::Nil)),
        ret: Ty::Void,
        trusted: false, conds: List::Nil,
        body: one(Stmt::Call(BUMP, SAT_NAME, Box::new(List::Cons(b(read(LOC, Ty::Struct(COUNTER))), Box::new(List::Nil))), 17)),
    };
    assert_eq!(bare_refusal(translate_function(&on_param, &all, &counter_table())), Refusal::WriteParam(LOC, 17));
    // q.c_.bump() on a field of a local
    let field = Expr::Field(b(Expr::Var(LOC, Ty::Struct(POINT))), FX);
    let on_field = Function {
        params: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(LOC, Ty::Struct(POINT), Expr::Construct(POINT, Box::new(List::Nil)), 22)),
            Box::new(one(Stmt::Call(BUMP, SAT_NAME, Box::new(List::Cons(b(field), Box::new(List::Nil))), 23)))),
        ..Function { name: SAT, line: 21, params: List::Nil, ret: Ty::Void, trusted: false, conds: List::Nil, body: List::Nil }
    };
    assert_eq!(bare_refusal(translate_function(&on_field, &all, &counter_table())), Refusal::NoTarget(23));
}

#[test]
fn a_void_function_ends_with_return_and_is_called_as_a_statement() {
    // void nothing() { return; }, and nothing(); in another function
    let nothing = Function { name: BUMP, line: 40, params: List::Nil, ret: Ty::Void, trusted: false, conds: List::Nil, body: one(Stmt::Exit(41)) };
    let Model::Full(m) = translate_function(&nothing, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Void);
    assert!(!m.writes);
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Exit), 0), Box::new(List::Nil)));
    let caller = Function {
        name: SAT,
        line: 44,
        params: List::Nil,
        ret: Ty::I32,
        trusted: false, conds: List::Nil,
        body: List::Cons(Box::new(Stmt::Call(BUMP, SAT_NAME, Box::new(List::Nil), 45)), Box::new(one(Stmt::Return(Expr::Lit(3, Ty::I32), 46)))),
    };
    let Model::Full(m) = translate_function(&caller, &fns(vec![nothing]), &List::Nil) else { panic!("a full model") };
    let List::Cons((call, _), _) = strip(m.body) else { panic!("a call") };
    assert_eq!(*call, DStmt::CallStmt(BUMP, List::Nil));
    // return; in a function that gives a value, and a local of void, are refused.
    assert_eq!(bare_refusal(translate_function(&with_n(one(Stmt::Exit(4))), &List::Nil, &List::Nil)), Refusal::Syntax(4));
    assert_eq!(translate_value_ty(Ty::Void, 3, &List::Nil), Err(Refusal::Syntax(3)));
}

#[test]
fn the_parser_reads_old() {
    // n_ == old(n_) + 1
    let toks = vec![Tok::Ident(CN), Tok::Op(BinOp::Eq), Tok::Old, Tok::LParen, Tok::Ident(CN), Tok::RParen, Tok::Op(BinOp::Add), Tok::Int(1)];
    let want = Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Bin(BinOp::Add, b(Expr::Old(b(Expr::Name(CN)))), b(Expr::Int(1)))));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
    assert_eq!(parse_contract(&vec![Tok::Old, Tok::Ident(CN)], 3), Err(Refusal::Syntax(3)));
}

#[test]
fn a_requires_line_of_a_constructor_has_no_object_yet() {
    // explicit Counter(int32_t n) with requires n_ < 1000, or requires valid(): the object is built only by the constructor.
    let table = members_table(Some(Ty::Bool), None);
    let ctor = |req: Expr| Function {
        name: CTOR,
        line: 9,
        params: List::Cons((X, Ty::I32), Box::new(List::Nil)),
        ret: Ty::This(COUNTER),
        trusted: false, conds: List::Cons((CondKind::Requires, req, 7, names(&[X])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Construct(COUNTER, Box::new(List::Cons(b(read(X, Ty::I32)), Box::new(List::Nil)))), 9)),
    };
    let field = ctor(Expr::Bin(BinOp::Lt, b(Expr::Name(CN)), b(Expr::Int(1000))));
    assert_eq!(bare_refusal(translate_function(&field, &List::Nil, &table)), Refusal::NoObject(CN, 7));
    let valid = ctor(Expr::Apply(VALID, Box::new(List::Nil)));
    assert_eq!(bare_refusal(translate_function(&valid, &List::Nil, &table)), Refusal::NoObject(VALID, 7));
}

const CAP: u32 = 180;
const LIMIT: u32 = 181;
const OPKEY: u32 = 182;
const F: u32 = 183;
const HOLDER: u32 = 184;
const FC: u32 = 185;

/// `struct CapAt { int32_t limit; }` with its `operator()` of the key OPKEY, pure when `pure` holds.
fn cap_table(pure: bool) -> Structs {
    let op = if pure { Some((Ty::I32, List::Cons((THIS, Ty::This(CAP)), Box::new(List::Cons((X, Ty::I32), Box::new(List::Nil)))))) } else { None };
    List::Cons((CAP, (4, List::Cons((LIMIT, Ty::I32), Box::new(List::Nil)), List::Cons((CALL_OP, (OPKEY, op)), Box::new(List::Nil)))), Box::new(List::Nil))
}

#[test]
fn a_conditional_chooses_a_branch_in_code_and_in_contracts() {
    // int32_t cap(int32_t x, int32_t limit) with ensures result == (x < limit ? x : limit), and return x < limit ? x : limit;
    let ps = List::Cons((X, Ty::I32), Box::new(List::Cons((LIMIT, Ty::I32), Box::new(List::Nil))));
    let cond = Expr::Cond(b(Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Name(LIMIT)))), b(Expr::Name(X)), b(Expr::Name(LIMIT)));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Paren(b(cond))));
    let code = Expr::Cond(b(Expr::Bin(BinOp::Lt, b(read(X, Ty::I32)), b(read(LIMIT, Ty::I32)))), b(read(X, Ty::I32)), b(read(LIMIT, Ty::I32)));
    let f = Function {
        name: SAT,
        line: 3,
        params: ps,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 2, names(&[X, LIMIT])), Box::new(List::Nil)),
        body: one(Stmt::Return(code, 4)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let v = |n| Box::new(DExpr::Var(n));
    let want = DExpr::Ite(Box::new(DExpr::Bin(BinOp::Lt, v(X), v(LIMIT))), v(X), v(LIMIT));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
    let i = |n| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::Ite(Box::new(DExpr::Bin(BinOp::Lt, i(X), i(LIMIT))), i(X), i(LIMIT))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A branch holds no call, as any expression of code.
    let call_in = Expr::Cond(b(Expr::Bool(true)), b(call(SUCC, vec![read(X, Ty::I32)], 4)), b(read(X, Ty::I32)));
    let f = Function { trusted: false, conds: List::Nil, body: one(Stmt::Return(call_in, 4)), ..f };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Place(4));
}

#[test]
fn the_parser_reads_a_conditional() {
    let (a, bb, c, d, e) = (Tok::Ident(1), Tok::Ident(2), Tok::Ident(3), Tok::Ident(60), Tok::Ident(61));
    let n = |x| b(Expr::Name(x));
    let (q, k) = (Tok::Question, Tok::Colon);
    // a ? b : c
    assert_eq!(parse_contract(&vec![a, q, bb, k, c], 3), Ok(Expr::Cond(n(1), n(2), n(3))));
    // a || b ? c : d is (a || b) ? c : d, and a ==> b ? c : d is a ==> (b ? c : d).
    assert_eq!(parse_contract(&vec![a, Tok::Op(BinOp::Or), bb, q, c, k, d], 3), Ok(Expr::Cond(b(Expr::Bin(BinOp::Or, n(1), n(2))), n(3), n(60))));
    assert_eq!(parse_contract(&vec![a, Tok::Op(BinOp::Implies), bb, q, c, k, d], 3), Ok(Expr::Bin(BinOp::Implies, n(1), b(Expr::Cond(n(2), n(3), n(60))))));
    // a ? b : c ? d : e groups to the right, and a ? b ? c : d : e reads the middle part to its colon.
    assert_eq!(parse_contract(&vec![a, q, bb, k, c, q, d, k, e], 3), Ok(Expr::Cond(n(1), n(2), b(Expr::Cond(n(3), n(60), n(61))))));
    assert_eq!(parse_contract(&vec![a, q, bb, q, c, k, d, k, e], 3), Ok(Expr::Cond(n(1), b(Expr::Cond(n(2), n(3), n(60))), n(61))));
    // A quantifier in the middle part ends at the colon.
    let fa = vec![a, q, Tok::Forall, Tok::Ident(60), Tok::ColonColon, bb, k, c];
    assert_eq!(parse_contract(&fa, 3), Ok(Expr::Cond(n(1), b(Expr::Forall(60, n(2))), n(3))));
    // No colon, no last part, or a colon with no question mark.
    assert_eq!(parse_contract(&vec![a, q, bb], 3), Err(Refusal::Syntax(3)));
    assert_eq!(parse_contract(&vec![a, q, bb, k], 3), Err(Refusal::Syntax(3)));
    assert_eq!(parse_contract(&vec![a, k, bb], 3), Err(Refusal::Syntax(3)));
}

#[test]
fn a_contract_calls_the_operator_of_a_functor() {
    // int32_t cap_twice(CapAt f, int32_t x) with ensures result == f(f(x))
    let ps = List::Cons((F, Ty::Struct(CAP)), Box::new(List::Cons((X, Ty::I32), Box::new(List::Nil))));
    let inner = Expr::Apply(F, Box::new(List::Cons(b(Expr::Name(X)), Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(F, Box::new(List::Cons(b(inner), Box::new(List::Nil))))));
    let f = Function {
        name: SAT,
        line: 3,
        params: ps,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 2, names(&[F, X])), Box::new(List::Nil)),
        body: one(Stmt::Return(read(X, Ty::I32), 4)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &cap_table(true)) else { panic!("a full model") };
    let op = |o: DExpr, arg: DExpr| {
        DExpr::AsInt(Box::new(DExpr::FCall(OPKEY, Box::new(List::Cons(o, Box::new(List::Cons(DExpr::Conv(DTy::Int32, Box::new(arg)), Box::new(List::Nil))))))))
    };
    let x = || DExpr::AsInt(Box::new(DExpr::Var(X)));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(op(DExpr::Var(F), op(DExpr::Var(F), x()))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // An operator() that is not pure is refused at the line.
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &cap_table(false))), Refusal::NotPure(CALL_OP, 2));
    // A field of the object: struct Wrap { CapAt c; } with int32_t Wrap::run(int32_t x) const and ensures result == c(x).
    let wrap = List::Cons((HOLDER, (8, List::Cons((FC, Ty::Struct(CAP)), Box::new(List::Nil)), List::Nil)), Box::new(cap_table(true)));
    let ps = List::Cons((THIS, Ty::This(HOLDER)), Box::new(List::Cons((X, Ty::I32), Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(FC, Box::new(List::Cons(b(Expr::Name(X)), Box::new(List::Nil))))));
    let g = Function {
        name: SAT,
        line: 10,
        params: ps,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 9, names(&[THIS, X])), Box::new(List::Nil)),
        body: one(Stmt::Return(read(X, Ty::I32), 11)),
    };
    let Model::Full(m) = translate_function(&g, &List::Nil, &wrap) else { panic!("a full model") };
    let List::Cons((first, _), _) = m.ensures else { panic!("an ensures line") };
    let obj = DExpr::Field(Box::new(DExpr::Var(THIS)), FC);
    assert_eq!(first, DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(op(obj, x()))));
}

#[test]
fn a_bound_name_is_no_function() {
    // int32_t f(CapAt c, int32_t x) with ensures forall c :: 0 <= c < 1 ==> c(x) == x
    let ps = List::Cons((F, Ty::Struct(CAP)), Box::new(List::Cons((X, Ty::I32), Box::new(List::Nil))));
    let range = Expr::Chain(BinOp::Le, BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(F)), b(Expr::Int(1)));
    let call = Expr::Apply(F, Box::new(List::Cons(b(Expr::Name(X)), Box::new(List::Nil))));
    let ens = Expr::Forall(F, b(Expr::Bin(BinOp::Implies, b(range), b(Expr::Bin(BinOp::Eq, b(call), b(Expr::Name(X)))))));
    let f = Function {
        name: SAT,
        line: 3,
        params: ps,
        ret: Ty::I32,
        trusted: false, conds: List::Cons((CondKind::Ensures, ens, 2, names(&[F, X])), Box::new(List::Nil)),
        body: one(Stmt::Return(read(X, Ty::I32), 4)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &cap_table(true))), Refusal::Syntax(2));
}

const YY: u32 = 190;
const LEM: u32 = 191;

#[test]
fn an_assert_line_states_a_fact_about_the_variables_in_scope() {
    // int32_t f(int32_t x) { int32_t y = x; //@ assert y == x  //@ apply L(y)  return y; }
    let fact = |e: Expr| Stmt::Assert(e, 5);
    let body = |s: Stmt| {
        List::Cons(
            Box::new(Stmt::Local(YY, Ty::I32, read(X, Ty::I32), 4)),
            Box::new(List::Cons(
                Box::new(s),
                Box::new(List::Cons(
                    Box::new(Stmt::Apply(LEM, Box::new(List::Cons(b(Expr::Name(YY)), Box::new(List::Nil))), 6)),
                    Box::new(one(Stmt::Return(read(YY, Ty::I32), 7))))))))
    };
    let f = |s: Stmt| Function { name: SAT, line: 3, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: body(s) };
    let Model::Full(m) = translate_function(&f(fact(Expr::Bin(BinOp::Eq, b(Expr::Name(YY)), b(Expr::Name(X))))), &List::Nil, &List::Nil) else {
        panic!("a full model")
    };
    let i = |n| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    let List::Cons((_, _), rest) = m.body else { panic!("a local") };
    let List::Cons((a, la), rest) = *rest else { panic!("an assert") };
    assert_eq!((*a, la), (DStmt::Assert(DExpr::Bin(BinOp::Eq, i(YY), i(X))), 5));
    let List::Cons((p, lp), _) = *rest else { panic!("an apply") };
    assert_eq!((*p, lp), (DStmt::Apply(LEM, List::Cons(DExpr::AsInt(Box::new(DExpr::Var(YY))), Box::new(List::Nil))), 6));
    // A name out of scope is no variable, and an assert line names no result.
    let out = fact(Expr::Bin(BinOp::Eq, b(Expr::Name(Q)), b(Expr::Int(0))));
    assert_eq!(bare_refusal(translate_function(&f(out), &List::Nil, &List::Nil)), Refusal::NoVar(Q, 5));
    let res = fact(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))));
    assert_eq!(bare_refusal(translate_function(&f(res), &List::Nil, &List::Nil)), Refusal::Syntax(5));
}

#[test]
fn a_contract_in_the_body_of_a_member_function_reads_the_object_as_the_body_leaves_it() {
    // void Counter::reset() with int32_t a = 0; then //@ assert n_ == 0 && old(n_) >= 0, and a loop with //@ invariant n_ == a.
    let this = |t: Ty| List::Cons((THIS, t), Box::new(List::Nil));
    let fact = Expr::Bin(BinOp::And, b(Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Int(0)))), b(Expr::Bin(BinOp::Ge, b(Expr::Old(b(Expr::Name(CN)))), b(Expr::Int(0)))));
    let inv = List::Cons((CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Name(A))), 13, List::Nil), Box::new(List::Nil));
    let body = List::Cons(
        Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(0, Ty::I32), 11)),
        Box::new(List::Cons(
            Box::new(Stmt::Assert(fact, 12)),
            Box::new(one(Stmt::While(Expr::Bool(false), Box::new(inv), Box::new(List::Nil), 14))))));
    let f = Function { name: BUMP, line: 10, params: this(Ty::ThisMut(COUNTER)), ret: Ty::Void, trusted: false, conds: List::Nil, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &counter_table()) else { panic!("a full model") };
    let field = |o: DExpr| Box::new(DExpr::AsInt(Box::new(DExpr::Field(Box::new(o), CN))));
    let List::Cons((_, _), rest) = m.body else { panic!("a local") };
    let List::Cons((a, _), rest) = *rest else { panic!("an assert") };
    let want = DExpr::Bin(
        BinOp::And,
        Box::new(DExpr::Bin(BinOp::Eq, field(DExpr::After), Box::new(DExpr::Lit(0)))),
        Box::new(DExpr::Bin(BinOp::Ge, field(DExpr::Var(THIS)), Box::new(DExpr::Lit(0)))),
    );
    assert_eq!(*a, DStmt::Assert(want));
    let List::Cons((w, _), _) = *rest else { panic!("a loop") };
    let DStmt::While(_, inv, _, _) = *w else { panic!("a while") };
    let local = Box::new(DExpr::AsInt(Box::new(DExpr::Var(A))));
    assert_eq!(strip_conds(inv), List::Cons((DExpr::Bin(BinOp::Eq, field(DExpr::After), local), 0), Box::new(List::Nil)));
    // In a const member function the object is this, and old() has no meaning.
    let body = List::Cons(
        Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(0, Ty::I32), 11)),
        Box::new(one(Stmt::Assert(Expr::Bin(BinOp::Eq, b(Expr::Name(CN)), b(Expr::Name(A))), 12))));
    let g = Function { params: this(Ty::This(COUNTER)), body, ..f };
    let Model::Full(m) = translate_function(&g, &List::Nil, &counter_table()) else { panic!("a full model") };
    let List::Cons((_, _), rest) = m.body else { panic!("a local") };
    let List::Cons((a, _), _) = *rest else { panic!("an assert") };
    assert_eq!(*a, DStmt::Assert(DExpr::Bin(BinOp::Eq, field(DExpr::Var(THIS)), Box::new(DExpr::AsInt(Box::new(DExpr::Var(A)))))));
    let old = Stmt::Assert(Expr::Bin(BinOp::Ge, b(Expr::Old(b(Expr::Name(CN)))), b(Expr::Int(0))), 12);
    let h = Function { body: one(old), ..g };
    assert_eq!(bare_refusal(translate_function(&h, &List::Nil, &counter_table())), Refusal::Syntax(12));
}

#[test]
fn a_trusted_function_is_a_method_with_its_contract_and_no_body() {
    // CPLUSP_TRUSTED uint32_t read_status() with ensures result <= 255, and a body that the translator has no rule for.
    let ens = Expr::Bin(BinOp::Le, b(Expr::Result), b(Expr::Int(255)));
    let f = Function {
        name: SAT,
        line: 8,
        params: List::Nil,
        ret: Ty::U32,
        trusted: true,
        conds: List::Cons((CondKind::Ensures, ens, 7, List::Nil), Box::new(List::Nil)),
        body: one(Stmt::Unknown(77, 9)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert!(m.trusted);
    assert_eq!(m.body, List::Nil);
    let want = DExpr::Bin(BinOp::Le, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::Lit(255)));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A function that is not trusted has its body, so the same body is refused.
    let g = Function { trusted: false, ..f };
    assert_eq!(bare_refusal(translate_function(&g, &List::Nil, &List::Nil)), Refusal::Construct(77, 9));
}

#[test]
fn a_trusted_member_function_is_never_pure() {
    // int32_t Counter::value() const { return n_; } marked trusted, and a const member whose ensures line calls value().
    let field = Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let value = Function { trusted: true, ..value_fn(one(Stmt::Return(field, 10))) };
    let user = Function {
        name: SAT,
        line: 20,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(VALUE, Box::new(List::Nil)))), 19, names(&[THIS])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 21)),
    };
    let List::Cons(Model::Full(m), rest) = translate_unit(&fns(vec![value, user]), &members_table(None, Some(Ty::I32))) else {
        panic!("a full model of value")
    };
    assert!(m.trusted);
    assert_eq!(m.function, None);
    let List::Cons(u, _) = *rest else { panic!("a model of the user") };
    assert_eq!(bare_refusal(u), Refusal::NotPure(VALUE, 19));
}

#[test]
fn three_small_integer_types_and_a_right_shift() {
    // int8_t to_byte(int32_t x) { return static_cast<int8_t>(x); }
    let cast = Expr::Cast(CastKind::Integral(Ty::I32, Ty::I8), b(read(X, Ty::I32)));
    let f = Function {
        name: SAT,
        line: 3,
        params: List::Cons((X, Ty::I32), Box::new(List::Nil)),
        ret: Ty::I8,
        trusted: false,
        conds: List::Nil,
        body: one(Stmt::Return(cast, 4)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Int8);
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Conv(DTy::Int8, Box::new(DExpr::Var(X))))), 0), Box::new(List::Nil)));
    assert_eq!(translate_ty(Ty::I16, 3), Ok(DTy::Int16));
    assert_eq!(translate_ty(Ty::U16, 3), Ok(DTy::UInt16));
    // A contract reads an int16_t as an exact integer.
    let ps = List::Cons((X, Ty::I16), Box::new(List::Nil));
    assert_eq!(translate_contract(&Expr::Name(X), &names(&[X]), &ps, Some(Ty::I16), &List::Nil, 2, &List::Nil), Ok(DExpr::AsInt(Box::new(DExpr::Var(X)))));
    // uint32_t shift(uint32_t x, uint32_t n) { return x >> n; }: the width is that of the type after promotion.
    let int = |n: u32| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    let shr = Expr::Shr(b(read(X, Ty::U32)), b(read(B, Ty::U32)), Ty::U32);
    assert_eq!(translate_code(&shr, 3), Ok(DExpr::ShrIn(int(X), int(B), DTy::UInt32, 32)));
    let wide = Expr::Shr(b(read(X, Ty::I64)), b(read(B, Ty::I32)), Ty::I64);
    assert_eq!(translate_code(&wide, 3), Ok(DExpr::ShrIn(int(X), int(B), DTy::Int64, 64)));
    // A shift of a bool has no rule.
    assert_eq!(translate_code(&Expr::Shr(b(Expr::Bool(true)), b(Expr::Bool(true)), Ty::Bool), 3), Err(Refusal::Convert(3)));
}

const DST: u32 = 190;
const SRC: u32 = 191;
const TAKE_REF: u32 = 192;
const NEXT: u32 = 193;
const FIRST: u32 = 194;

fn mut32() -> Ty {
    Ty::Mut(Scalar::I32)
}

fn objs(v: &[Obj]) -> Objs {
    v.iter().rev().fold(List::Nil, |rest, o| List::Cons(*o, Box::new(rest)))
}

fn dargs(v: Vec<DExpr>) -> DArgs {
    v.into_iter().rev().fold(List::Nil, |rest, d| List::Cons(d, Box::new(rest)))
}

fn int_params(v: &[u32]) -> DParams {
    v.iter().rev().fold(List::Nil, |rest, n| List::Cons((*n, DTy::Int32), Box::new(rest)))
}

/// `//@ modifies` lines that name each of `v`, at line 5 above a declaration with the parameters `ps`.
fn modifies(v: &[u32], ps: &[u32], rest: Conds) -> Conds {
    v.iter().rev().fold(rest, |r, n| List::Cons((CondKind::Modifies, Expr::Name(*n), 5, names(ps)), Box::new(r)))
}

/// `void take(int32_t& dst, int32_t& src)` with modifies dst, src and ensures dst == old(src) && src == 0, and a body of
/// dst = src; src = 0;
fn take_ref() -> Function {
    let ens = Expr::Bin(
        BinOp::And,
        b(Expr::Bin(BinOp::Eq, b(Expr::Name(DST)), b(Expr::Old(b(Expr::Name(SRC)))))),
        b(Expr::Bin(BinOp::Eq, b(Expr::Name(SRC)), b(Expr::Int(0)))),
    );
    Function {
        name: TAKE_REF,
        line: 8,
        params: List::Cons((DST, mut32()), Box::new(List::Cons((SRC, mut32()), Box::new(List::Nil)))),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[DST, SRC], &[DST, SRC], List::Cons((CondKind::Ensures, ens, 7, names(&[DST, SRC])), Box::new(List::Nil))),
        body: List::Cons(
            Box::new(Stmt::Assign(DST, read(SRC, mut32()), 9)),
            Box::new(one(Stmt::Assign(SRC, Expr::Lit(0, Ty::I32), 10)))),
    }
}

#[test]
fn a_reference_parameter_on_the_modifies_line_takes_a_value_in_and_gives_it_back() {
    let Model::Full(m) = translate_function(&take_ref(), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.params, int_params(&[DST, SRC]));
    assert_eq!(m.outs, int_params(&[DST, SRC]));
    assert!(!m.writes);
    // The body reads and writes the value after: dst' and src'.
    assert_eq!(
        strip(m.body),
        List::Cons((Box::new(DStmt::SetOut(DST, DExpr::Out(SRC))), 0), Box::new(List::Cons((Box::new(DStmt::SetOut(SRC, lit32(0))), 0), Box::new(List::Nil))))
    );
    // An ensures line reads the value after the call, and old() the value before.
    let int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Bin(
        BinOp::And,
        Box::new(DExpr::Bin(BinOp::Eq, int(DExpr::Out(DST)), int(DExpr::Var(SRC)))),
        Box::new(DExpr::Bin(BinOp::Eq, int(DExpr::Out(SRC)), Box::new(DExpr::Lit(0)))),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn a_requires_line_reads_a_reference_parameter_before_the_call_and_old_has_no_place_there() {
    // //@ requires x < 1000 on void bump(int32_t& x) with modifies x
    let req = Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Int(1000)));
    let f = Function {
        name: TAKE_REF,
        line: 8,
        params: List::Cons((X, mut32()), Box::new(List::Nil)),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[X], &[X], List::Cons((CondKind::Requires, req, 6, names(&[X])), Box::new(List::Nil))),
        body: one(Stmt::Step(X, Ty::I32, true, 9)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Lt, Box::new(DExpr::AsInt(Box::new(DExpr::Var(X)))), Box::new(DExpr::Lit(1000)));
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
    // ++x writes the value after.
    let step = DStmt::SetOut(X, DExpr::Bin(BinOp::Add, Box::new(DExpr::Out(X)), Box::new(lit32(1))));
    assert_eq!(strip(m.body), List::Cons((Box::new(step), 0), Box::new(List::Nil)));
    let old = Expr::Bin(BinOp::Lt, b(Expr::Old(b(Expr::Name(X)))), b(Expr::Int(1000)));
    let g = Function { conds: modifies(&[X], &[X], List::Cons((CondKind::Requires, old, 6, names(&[X])), Box::new(List::Nil))), ..f };
    assert_eq!(bare_refusal(translate_function(&g, &List::Nil, &List::Nil)), Refusal::Syntax(6));
}

#[test]
fn the_modifies_line_names_each_reference_parameter_and_nothing_else() {
    // A name on the modifies line that is a parameter by value.
    let by_value = Function {
        conds: modifies(&[X], &[X], List::Nil),
        ..with_n(one(Stmt::Return(read(X, Ty::I32), 4)))
    };
    assert_eq!(translate_function(&by_value, &List::Nil, &List::Nil), Model::Refused(Refusal::NotRef(X, 5)));
    // A reference parameter that the modifies line does not name.
    let unlisted = Function { conds: modifies(&[DST], &[DST, SRC], List::Nil), ..take_ref() };
    assert_eq!(translate_function(&unlisted, &List::Nil, &List::Nil), Model::Refused(Refusal::Unlisted(SRC, 8)));
    // A reference parameter is a parameter only. It is no result type.
    let ret = Function { ret: mut32(), conds: List::Nil, ..with_n(one(Stmt::Return(read(X, Ty::I32), 4))) };
    assert!(matches!(translate_function(&ret, &List::Nil, &List::Nil), Model::Refused(_)));
}

#[test]
fn a_call_writes_back_each_argument_of_a_reference_parameter() {
    let all = fns(vec![take_ref()]);
    // int32_t a = 1; int32_t b = 5; take(a, b); return a;
    let user = Function {
        name: SAT,
        line: 20,
        params: List::Nil,
        ret: Ty::I32,
        trusted: false,
        conds: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(1, Ty::I32), 21)),
            Box::new(List::Cons(
                Box::new(Stmt::Local(B, Ty::I32, Expr::Lit(5, Ty::I32), 22)),
                Box::new(List::Cons(
                    Box::new(Stmt::Call(TAKE_REF, SAT_NAME, Box::new(List::Cons(b(var(A)), Box::new(List::Cons(b(var(B)), Box::new(List::Nil))))), 23)),
                    Box::new(one(Stmt::Return(read(A, Ty::I32), 24)))))))),
    };
    let Model::Full(m) = translate_function(&user, &all, &List::Nil) else { panic!("a full model") };
    let List::Cons((_, _), rest) = strip(m.body) else { panic!("a body") };
    let List::Cons((_, _), rest) = *rest else { panic!("a local") };
    let List::Cons((update, _), _) = *rest else { panic!("an update") };
    assert_eq!(*update, DStmt::Update(objs(&[Obj::Local(A), Obj::Local(B)]), TAKE_REF, dargs(vec![DExpr::Var(A), DExpr::Var(B)])));
}

/// `int32_t next(int32_t& x)` with modifies x, and a body of return 0.
fn next_fn() -> Function {
    Function {
        name: NEXT,
        line: 30,
        params: List::Cons((X, mut32()), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: modifies(&[X], &[X], List::Nil),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 31)),
    }
}

#[test]
fn a_reference_parameter_of_the_caller_is_written_back_and_a_call_that_gives_a_value_sets_a_local() {
    let all = fns(vec![next_fn()]);
    // int32_t two(int32_t& x) with modifies x: int32_t first = next(x); return first;
    let user = Function {
        name: SAT,
        line: 40,
        params: List::Cons((X, mut32()), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: modifies(&[X], &[X], List::Nil),
        body: List::Cons(
            Box::new(Stmt::Local(FIRST, Ty::I32, call(NEXT, vec![Expr::Var(X, mut32())], 41), 41)),
            Box::new(one(Stmt::Return(read(FIRST, Ty::I32), 42)))),
    };
    let Model::Full(m) = translate_function(&user, &all, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.outs, int_params(&[X]));
    let List::Cons((local, _), _) = strip(m.body) else { panic!("a body") };
    assert_eq!(*local, DStmt::LocalUpdate(FIRST, DTy::Int32, objs(&[Obj::Out(X)]), NEXT, dargs(vec![DExpr::Out(X)])));
    // A call that writes x runs first inside an expression too, into a temporary, decision 0177: return next(x) + 1;
    let inside = Expr::Bin(BinOp::Add, b(call(NEXT, vec![Expr::Var(X, mut32())], 43)), b(Expr::Lit(1, Ty::I32)));
    let g = Function { body: one(Stmt::Return(inside, 43)), ..user };
    let Model::Full(m) = translate_function(&g, &all, &List::Nil) else { panic!("a full model") };
    let pre = List::Cons(DPre::Update(0, DTy::Int32, objs(&[Obj::Out(X)]), NEXT, dargs(vec![DExpr::Out(X)])), Box::new(List::Nil));
    let want = DStmt::Pre(pre, Box::new(DStmt::Return(DExpr::Bin(BinOp::Add, Box::new(DExpr::Temp(0)), Box::new(lit32(1))))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
}

#[test]
fn a_call_that_writes_a_parameter_by_value_or_a_field_is_refused_at_its_line() {
    let all = fns(vec![next_fn()]);
    // void f(int32_t y) { next(y); }
    let by_value = Function {
        name: SAT,
        line: 50,
        params: List::Cons((Q, Ty::I32), Box::new(List::Nil)),
        ret: Ty::Void,
        trusted: false,
        conds: List::Nil,
        body: one(Stmt::Local(FIRST, Ty::I32, call(NEXT, vec![var(Q)], 51), 51)),
    };
    assert_eq!(bare_refusal(translate_function(&by_value, &all, &point_table())), Refusal::WriteParam(Q, 51));
    // next(q.x) on a field of a local
    let field = Expr::Field(b(Expr::Var(LOC, Ty::Struct(POINT))), FX);
    let on_field = Function {
        params: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(LOC, Ty::Struct(POINT), Expr::Construct(POINT, Box::new(List::Nil)), 52)),
            Box::new(one(Stmt::Local(FIRST, Ty::I32, call(NEXT, vec![field], 53), 53)))),
        ..by_value
    };
    assert_eq!(bare_refusal(translate_function(&on_field, &all, &point_table())), Refusal::NoTarget(53));
}

#[test]
fn a_reference_to_a_struct_writes_the_whole_value_and_each_field() {
    // void swapped(Point& out, const Point& p) with modifies out: out = p; out.x = 0;
    let f = Function {
        name: SAT,
        line: 60,
        params: List::Cons((DST, Ty::Mut(Scalar::Struct(POINT))), Box::new(List::Cons((P, Ty::Struct(POINT)), Box::new(List::Nil)))),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[DST], &[DST, P], List::Nil),
        body: List::Cons(
            Box::new(Stmt::Assign(DST, read(P, Ty::Struct(POINT)), 61)),
            Box::new(one(Stmt::SetRefField(DST, FX, Expr::Lit(0, Ty::I32), 62)))),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &point_table()) else { panic!("a full model") };
    assert_eq!(m.outs, List::Cons((DST, DTy::Struct(POINT)), Box::new(List::Nil)));
    assert_eq!(
        strip(m.body),
        List::Cons((Box::new(DStmt::SetOut(DST, DExpr::Var(P))), 0), Box::new(List::Cons((Box::new(DStmt::SetOutField(DST, FX, lit32(0))), 0), Box::new(List::Nil))))
    );
}

const KIND: u32 = 200;
const K: u32 = 201;
const WEIGHT: u32 = 202;

fn kind() -> Ty {
    Ty::Enum(KIND)
}

/// `int32_t weight(Kind k)` with ensures result == (k == Kind::Small ? 1 : 10), and a switch with a case for each enumerator.
fn weight_fn() -> Function {
    let ens = Expr::Bin(
        BinOp::Eq,
        b(Expr::Result),
        b(Expr::Cond(b(Expr::Bin(BinOp::Eq, b(Expr::Name(K)), b(Expr::Enumerator(KIND, 0)))), b(Expr::Int(1)), b(Expr::Int(10)))),
    );
    let cases = List::Cons((0, Box::new(one(Stmt::Return(Expr::Lit(1, Ty::I32), 10)))), Box::new(List::Cons((1, Box::new(one(Stmt::Return(Expr::Lit(10, Ty::I32), 12)))), Box::new(List::Nil))));
    Function {
        name: WEIGHT,
        line: 7,
        params: List::Cons((K, kind()), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, ens, 6, names(&[K])), Box::new(List::Nil)),
        body: List::Cons(
            Box::new(Stmt::Switch(read(K, kind()), KIND, Box::new(cases), 8)),
            Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 14)))),
    }
}

#[test]
fn a_switch_over_an_enum_is_a_match_and_an_enumerator_is_a_constructor() {
    let Model::Full(m) = translate_function(&weight_fn(), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.params, List::Cons((K, DTy::Enum(KIND)), Box::new(List::Nil)));
    let cases = List::Cons((0, Box::new(List::Cons((Box::new(DStmt::Return(lit32(1))), 10), Box::new(List::Nil)))), Box::new(List::Cons((1, Box::new(List::Cons((Box::new(DStmt::Return(lit32(10))), 12), Box::new(List::Nil)))), Box::new(List::Nil))));
    // The cases keep their places, so a failure inside one maps to its line.
    assert_eq!(
        m.body,
        List::Cons((Box::new(DStmt::Match(DExpr::Var(K), KIND, Box::new(cases))), 8), Box::new(List::Cons((Box::new(DStmt::Return(lit32(0))), 14), Box::new(List::Nil))))
    );
    // An enum is no integer, so a contract reads it as itself.
    let want = DExpr::Bin(
        BinOp::Eq,
        Box::new(DExpr::AsInt(Box::new(DExpr::Result))),
        Box::new(DExpr::Ite(
            Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Var(K)), Box::new(DExpr::Enumerator(KIND, 0)))),
            Box::new(DExpr::Lit(1)),
            Box::new(DExpr::Lit(10)),
        )),
    );
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

#[test]
fn an_enum_is_a_value_of_a_local_and_a_result() {
    // Kind pick() { Kind k = Kind::Small; return k; }
    let f = Function {
        name: WEIGHT,
        line: 20,
        params: List::Nil,
        ret: kind(),
        trusted: false,
        conds: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(K, kind(), Expr::Enumerator(KIND, 0), 21)),
            Box::new(one(Stmt::Return(read(K, kind()), 22)))),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Enum(KIND));
    assert_eq!(
        strip(m.body),
        List::Cons((Box::new(DStmt::Local(K, DTy::Enum(KIND), DExpr::Enumerator(KIND, 0))), 0), Box::new(List::Cons((Box::new(DStmt::Return(DExpr::Var(K))), 0), Box::new(List::Nil))))
    );
}

#[test]
fn a_contract_reads_an_enumerator_by_its_token() {
    let toks = vec![Tok::Ident(K), Tok::Op(BinOp::Eq), Tok::Enumerator(KIND, 1)];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Bin(BinOp::Eq, b(Expr::Name(K)), b(Expr::Enumerator(KIND, 1)))));
}

#[test]
fn an_order_of_enums_in_a_contract_is_refused() {
    // bool below(Kind k) with ensures k < Kind::Large ==> result: Dafny would read `<` as an order of rank it does not know, decisions 0114, 0115.
    for op in [BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
        let line = Expr::Bin(BinOp::Implies, b(Expr::Bin(op, b(Expr::Name(K)), b(Expr::Enumerator(KIND, 1)))), b(Expr::Result));
        let f = Function {
            name: WEIGHT,
            line: 31,
            params: List::Cons((K, kind()), Box::new(List::Nil)),
            ret: Ty::Bool,
            trusted: false,
            conds: List::Cons((CondKind::Ensures, line, 30, names(&[K])), Box::new(List::Nil)),
            body: one(Stmt::Return(Expr::Bool(true), 32)),
        };
        assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(30), "{op:?}");
    }
    // An order of two enumerators, with no name, is refused too.
    let f = Function {
        name: WEIGHT,
        line: 31,
        params: List::Cons((K, kind()), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Lt, b(Expr::Enumerator(KIND, 0)), b(Expr::Enumerator(KIND, 1))), 30, names(&[K])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Bool(true), 32)),
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(30));
}

/// A chain of three or more comparisons is the chains of two that overlap, joined by `&&`, decision 0131.
#[test]
fn a_longer_chain_is_the_chains_of_two_that_overlap() {
    let chain = |o1, o2, x: Expr, y: Expr, z: Expr| Expr::Chain(o1, o2, b(x), b(y), b(z));
    let and = |x: Expr, y: Expr| Expr::Bin(BinOp::And, b(x), b(y));
    let (i, j, n) = (70, 71, 72);
    // 0 <= i < j < n
    let toks = vec![Tok::Int(0), Tok::Op(BinOp::Le), Tok::Ident(i), Tok::Op(BinOp::Lt), Tok::Ident(j), Tok::Op(BinOp::Lt), Tok::Ident(n)];
    assert_eq!(
        parse_contract(&toks, 3),
        Ok(and(chain(BinOp::Le, BinOp::Lt, Expr::Int(0), Expr::Name(i), Expr::Name(j)), chain(BinOp::Lt, BinOp::Lt, Expr::Name(i), Expr::Name(j), Expr::Name(n))))
    );
    // 0 < i <= j < n > 1: each turn of direction is in one chain of two, which the translator refuses.
    let toks = vec![
        Tok::Int(0), Tok::Op(BinOp::Lt), Tok::Ident(i), Tok::Op(BinOp::Le), Tok::Ident(j), Tok::Op(BinOp::Lt), Tok::Ident(n),
        Tok::Op(BinOp::Gt), Tok::Int(1),
    ];
    assert_eq!(
        parse_contract(&toks, 3),
        Ok(and(
            chain(BinOp::Lt, BinOp::Le, Expr::Int(0), Expr::Name(i), Expr::Name(j)),
            and(
                chain(BinOp::Le, BinOp::Lt, Expr::Name(i), Expr::Name(j), Expr::Name(n)),
                chain(BinOp::Lt, BinOp::Gt, Expr::Name(j), Expr::Name(n), Expr::Int(1))
            )
        ))
    );
    // a + 1 < b < c ==> x: each term is a sum, and the chain stops at the implication.
    let toks = vec![
        Tok::Ident(A), Tok::Op(BinOp::Add), Tok::Int(1), Tok::Op(BinOp::Lt), Tok::Ident(B), Tok::Op(BinOp::Lt), Tok::Ident(i),
        Tok::Op(BinOp::Lt), Tok::Ident(j), Tok::Op(BinOp::Implies), Tok::Ident(X),
    ];
    let sum = Expr::Bin(BinOp::Add, b(Expr::Name(A)), b(Expr::Int(1)));
    assert_eq!(
        parse_contract(&toks, 3),
        Ok(Expr::Bin(
            BinOp::Implies,
            b(and(chain(BinOp::Lt, BinOp::Lt, sum, Expr::Name(B), Expr::Name(i)), chain(BinOp::Lt, BinOp::Lt, Expr::Name(B), Expr::Name(i), Expr::Name(j)))),
            b(Expr::Name(X))
        ))
    );
}

/// `*o` is `o.value()`. It binds tighter than any operator and looser than a postfix, as in C++, decision 0131.
#[test]
fn a_star_before_a_term_reads_the_value() {
    let value = |x: Expr| Expr::Value(b(x));
    // *result < n && a[*result] == x
    let n = 72;
    let toks = vec![
        Tok::Op(BinOp::Mul), Tok::Result, Tok::Op(BinOp::Lt), Tok::Ident(n), Tok::Op(BinOp::And),
        Tok::Ident(A), Tok::LBracket, Tok::Op(BinOp::Mul), Tok::Result, Tok::RBracket, Tok::Op(BinOp::Eq), Tok::Ident(X),
    ];
    assert_eq!(
        parse_contract(&toks, 3),
        Ok(Expr::Bin(
            BinOp::And,
            b(Expr::Bin(BinOp::Lt, b(value(Expr::Result)), b(Expr::Name(n)))),
            b(Expr::Bin(BinOp::Eq, b(Expr::Index(b(Expr::Name(A)), b(value(Expr::Result)))), b(Expr::Name(X))))
        ))
    );
    // a * *b and *a[1]
    let toks = vec![Tok::Ident(A), Tok::Op(BinOp::Mul), Tok::Op(BinOp::Mul), Tok::Ident(B)];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Bin(BinOp::Mul, b(Expr::Name(A)), b(value(Expr::Name(B))))));
    let toks = vec![Tok::Op(BinOp::Mul), Tok::Ident(A), Tok::LBracket, Tok::Int(1), Tok::RBracket];
    assert_eq!(parse_contract(&toks, 3), Ok(value(Expr::Index(b(Expr::Name(A)), b(Expr::Int(1))))));
    // A lone star and a star at the end are refused.
    assert_eq!(parse_contract(&vec![Tok::Op(BinOp::Mul)], 5), Err(Refusal::Syntax(5)));
    assert_eq!(parse_contract(&vec![Tok::Ident(A), Tok::Op(BinOp::Mul)], 6), Err(Refusal::Syntax(6)));
}

/// `o->f` is `o.value().f`, a postfix like `.f`, decision 0137. After `->` comes a name, and anything else refuses the line.
#[test]
fn the_arrow_reads_a_field_of_the_value() {
    let lo = 90;
    let toks = vec![Tok::Result, Tok::Arrow, Tok::Ident(lo), Tok::Op(BinOp::Eq), Tok::Ident(A), Tok::Arrow, Tok::Ident(lo), Tok::Arrow, Tok::Ident(B)];
    let field = |o: Expr, f: u32| Expr::Field(b(Expr::Value(b(o))), f);
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Bin(BinOp::Eq, b(field(Expr::Result, lo)), b(field(field(Expr::Name(A), lo), B)))));
    // a->b[0] and -a->b: the arrow binds as a postfix.
    let toks = vec![Tok::Op(BinOp::Sub), Tok::Ident(A), Tok::Arrow, Tok::Ident(B), Tok::LBracket, Tok::Int(0), Tok::RBracket];
    assert_eq!(parse_contract(&toks, 3), Ok(Expr::Neg(b(Expr::Index(b(field(Expr::Name(A), B)), b(Expr::Int(0)))))));
    assert_eq!(parse_contract(&vec![Tok::Ident(A), Tok::Arrow], 4), Err(Refusal::Syntax(4)));
    assert_eq!(parse_contract(&vec![Tok::Ident(A), Tok::Arrow, Tok::Int(1)], 5), Err(Refusal::Syntax(5)));
    assert_eq!(parse_contract(&vec![Tok::Arrow, Tok::Ident(A)], 6), Err(Refusal::Syntax(6)));
}

/// `p == nullptr` and `p != nullptr` test an optional for a value, in a contract and in code, with nullptr on either side, decision
/// 0140. A comparison of nullptr with a value that is no optional is refused.
#[test]
fn a_comparison_with_nullptr_tests_for_a_value() {
    assert_eq!(parse_contract(&vec![Tok::Ident(A), Tok::Op(BinOp::Ne), Tok::Nullptr], 3), Ok(Expr::Bin(BinOp::Ne, b(Expr::Name(A)), b(Expr::Nullopt))));
    let some = || DExpr::IsSome(Box::new(DExpr::Var(A)));
    let none = || DExpr::Not(Box::new(some()));
    let req = |e: Expr, l: u32| (CondKind::Requires, e, l, names(&[A, B]));
    let f = Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, Ty::Ptr(Scalar::I32)), Box::new(List::Cons((B, Ty::I32), Box::new(List::Nil)))),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons(
            req(Expr::Bin(BinOp::Ne, b(Expr::Name(A)), b(Expr::Nullopt)), 6),
            Box::new(List::Cons(req(Expr::Bin(BinOp::Eq, b(Expr::Nullopt), b(Expr::Name(A))), 7), Box::new(List::Nil))),
        ),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 11)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip_conds(m.requires), List::Cons((some(), 0), Box::new(List::Cons((none(), 0), Box::new(List::Nil)))));
    let o = || b(Expr::Var(A, Ty::Ptr(Scalar::I32)));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Eq, o(), b(Expr::Nullopt)), 3), Ok(none()));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Ne, b(Expr::Nullopt), o()), 3), Ok(some()));
    // b == nullptr, with b an int32_t, is refused.
    let f = Function { conds: List::Cons(req(Expr::Bin(BinOp::Eq, b(Expr::Name(B)), b(Expr::Nullopt)), 6), Box::new(List::Nil)), ..f };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(6));
}

/// Two pointers do not compare, and an optional is no pointer, decision 0141. In a contract, `p == q`, `p < q` and `o != nullptr`
/// are refused. In code, a comparison of two pointers is refused.
#[test]
fn two_pointers_do_not_compare() {
    let c = 72;
    let ptr = Ty::Ptr(Scalar::I32);
    let f = |e: Expr| Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, ptr), Box::new(List::Cons((B, ptr), Box::new(List::Cons((c, Ty::Opt(Scalar::I32)), Box::new(List::Nil)))))),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Requires, e, 6, names(&[A, B, c])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 11)),
    };
    for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Ge] {
        let e = Expr::Bin(op, b(Expr::Name(A)), b(Expr::Name(B)));
        assert_eq!(bare_refusal(translate_function(&f(e), &List::Nil, &List::Nil)), Refusal::Syntax(6), "{op:?}");
    }
    let e = Expr::Bin(BinOp::Ne, b(Expr::Name(c)), b(Expr::Nullopt));
    assert_eq!(bare_refusal(translate_function(&f(e), &List::Nil, &List::Nil)), Refusal::Syntax(6));
    // *p and p->f still read a pointer in a contract.
    let e = Expr::Bin(BinOp::Eq, b(Expr::Value(b(Expr::Name(A)))), b(Expr::Int(1)));
    assert!(matches!(translate_function(&f(e), &List::Nil, &List::Nil), Model::Full(_)));
    let p = || b(Expr::Var(A, ptr));
    let q = || b(Expr::Var(B, ptr));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Eq, p(), q()), 3), Err(Refusal::Syntax(3)));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Lt, p(), q()), 3), Err(Refusal::Syntax(3)));
}

/// A unique_ptr is `Own(T)`, decision 0142: an Option in Dafny, a parameter, a local or a result, but no field. Two of them do not
/// compare, and the test against nullptr takes one.
#[test]
fn a_unique_ptr_is_an_owned_optional() {
    let own = Ty::Own(Scalar::I32);
    assert_eq!(translate_ty(own, 3), Ok(DTy::Opt(Scalar::I32)));
    assert_eq!(translate_value_ty(own, 3, &List::Nil), Ok(DTy::Opt(Scalar::I32)));
    assert_eq!(param_ty(own, 3, &List::Nil), Ok(DTy::Opt(Scalar::I32)));
    assert_eq!(translate_value_ty(Ty::Own(Scalar::Struct(NODE)), 3, &node_table()), Err(Refusal::HoldsSeq(3)));
    let field = List::Cons((POINT, (4, List::Cons((FX, own), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    assert_eq!(translate_structs(&field), List::Cons(Err(Refusal::Element(4)), Box::new(List::Nil)));
    let f = |e: Expr| Function {
        name: SAT,
        line: 10,
        params: List::Cons((A, own), Box::new(List::Cons((B, own), Box::new(List::Nil)))),
        ret: own,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, e, 6, names(&[A, B])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Var(A, own), 11)),
    };
    // ensures result != nullptr
    let Model::Full(m) = translate_function(&f(Expr::Bin(BinOp::Ne, b(Expr::Result), b(Expr::Nullopt))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::IsSome(Box::new(DExpr::Result)), 0), Box::new(List::Nil)));
    // ensures a == b, and a < b
    for op in [BinOp::Eq, BinOp::Lt] {
        let e = Expr::Bin(op, b(Expr::Name(A)), b(Expr::Name(B)));
        assert_eq!(bare_refusal(translate_function(&f(e), &List::Nil, &List::Nil)), Refusal::Syntax(6), "{op:?}");
    }
    let p = || b(Expr::Var(A, own));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Eq, p(), b(Expr::Var(B, own))), 3), Err(Refusal::Syntax(3)));
    assert_eq!(translate_code(&Expr::Bin(BinOp::Eq, p(), b(Expr::Nullopt)), 3), Ok(DExpr::Not(Box::new(DExpr::IsSome(Box::new(DExpr::Var(A)))))));
}

const RV: u32 = 210;
const RX: u32 = 211;
const RI: u32 = 212;
const RFRESH: u32 = 213;
const RT: u32 = 214;

/// The statement at place `n` of a translated body.
fn nth(ss: &DStmts, n: usize) -> &DStmt {
    match ss {
        List::Cons((s, _), rest) => if n == 0 { s } else { nth(rest, n - 1) },
        List::Nil => panic!("no statement {n}"),
    }
}

fn dlen<T>(l: &List<T>) -> usize {
    match l {
        List::Nil => 0,
        List::Cons(_, rest) => 1 + dlen(rest),
    }
}

/// `int32_t t = 0; //@ index i (if any) for (T x : v) { t = x; } return t;` with `v` a span parameter, decision 0143.
fn ranged(conds: Conds, xt: Ty, seq: Expr, before: Option<Stmt>) -> Function {
    let range = Stmt::RangeFor(RFRESH, RX, xt, seq, Box::new(conds), Box::new(one(Stmt::Assign(RT, Expr::Var(RX, Ty::I32), 7))), 6);
    let mut body = List::Cons(Box::new(Stmt::Return(Expr::Var(RT, Ty::I32), 9)), Box::new(List::Nil));
    body = List::Cons(Box::new(range), Box::new(body));
    body = List::Cons(Box::new(Stmt::Local(RT, Ty::I32, Expr::Lit(0, Ty::I32), 4)), Box::new(body));
    if let Some(s) = before {
        body = List::Cons(Box::new(s), Box::new(body));
    }
    Function {
        name: SAT,
        line: 3,
        params: List::Cons((RV, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Nil,
        body,
    }
}

fn index_line(n: u32, l: u32) -> Conds {
    List::Cons((CondKind::Index, Expr::Name(n), l, names(&[RV, RT])), Box::new(List::Nil))
}

/// A range-for is a for loop over the indexes, decision 0143: the index from the index line or the fresh name of the shell, the
/// invariant `i <= v.size()` and the decreases `v.size() - i` from the core, and `x` as the first statement of each turn.
#[test]
fn a_range_for_is_a_for_loop_over_the_indexes() {
    let v = || Expr::Var(RV, Ty::Seq(Scalar::I32, Extent::Dynamic));
    for (conds, want) in [(index_line(RI, 5), RI), (List::Nil, RFRESH)] {
        let Model::Full(m) = translate_function(&ranged(conds, Ty::I32, v(), None), &List::Nil, &List::Nil) else { panic!("a full model") };
        let body = strip(m.body);
        let DStmt::For(init, _, _, inv, dec, turn, _, _) = nth(&body, 1) else { panic!("a for loop: {body:?}") };
        assert!(matches!(&**init, DStmt::Local(n, DTy::UInt64, _) if *n == want), "{init:?}");
        assert_eq!((dlen(inv), dlen(dec)), (1, 1));
        assert_eq!(nth(turn, 0), &DStmt::Local(RX, DTy::Int32, DExpr::Index(Box::new(DExpr::Var(RV)), Box::new(DExpr::Var(want)))));
        assert!(matches!(nth(turn, 1), DStmt::Assign(t, _) if *t == RT));
    }
}

/// An index line elsewhere is in the wrong place, an index name the function has is refused, and so are a range that is no sequence
/// parameter and a loop variable of another type, decision 0143.
#[test]
fn a_range_for_refuses_what_it_cannot_read() {
    let v = || Expr::Var(RV, Ty::Seq(Scalar::I32, Extent::Dynamic));
    // index line above a while loop
    let w = Stmt::While(Expr::Bool(false), Box::new(index_line(RI, 5)), Box::new(List::Nil), 6);
    let f = Function { body: List::Cons(Box::new(w), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 9)))), ..ranged(List::Nil, Ty::I32, v(), None) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Misplaced(5));
    // index line above a function
    let f = Function { conds: index_line(RI, 2), ..ranged(List::Nil, Ty::I32, v(), None) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Misplaced(2));
    // an index that is a parameter, or a local before the loop
    assert_eq!(bare_refusal(translate_function(&ranged(index_line(RV, 5), Ty::I32, v(), None), &List::Nil, &List::Nil)), Refusal::IndexName(RV, 5));
    let before = Stmt::Local(RI, Ty::I32, Expr::Lit(0, Ty::I32), 2);
    assert_eq!(bare_refusal(translate_function(&ranged(index_line(RI, 5), Ty::I32, v(), Some(before)), &List::Nil, &List::Nil)), Refusal::IndexName(RI, 5));
    // a range that is no variable, and a loop variable of another type
    let field = Expr::Field(b(v()), FV);
    assert_eq!(bare_refusal(translate_function(&ranged(List::Nil, Ty::I32, field, None), &List::Nil, &List::Nil)), Refusal::Syntax(6));
    assert_eq!(bare_refusal(translate_function(&ranged(List::Nil, Ty::I64, v(), None), &List::Nil, &List::Nil)), Refusal::Syntax(6));
}

const RSELF: u32 = 215;

/// An index named as a field of the object of a method is a name the function already has, decision 0144.
#[test]
fn an_index_is_no_field_of_the_object() {
    let v = || Expr::Var(RV, Ty::Seq(Scalar::I32, Extent::Dynamic));
    let table = List::Cons((POINT, (4, List::Cons((FX, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let f = ranged(index_line(FX, 5), Ty::I32, v(), None);
    let f = Function { params: List::Cons((RSELF, Ty::This(POINT)), Box::new(f.params)), ..f };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &table)), Refusal::IndexName(FX, 5));
}

const WV: u32 = 220;
const WI: u32 = 221;
const WX: u32 = 222;

/// `void write_at(std::vector<int32_t>& v, size_t i, int32_t x) { v[i] = x; }` with `modifies v`, decision 0145.
fn write_at(body: Stmts) -> Function {
    let vec = Ty::MutSeq(Scalar::I32);
    Function {
        name: SAT,
        line: 5,
        params: List::Cons((WV, vec), Box::new(List::Cons((WI, Ty::U64), Box::new(List::Cons((WX, Ty::I32), Box::new(List::Nil)))))),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[WV], &[WV, WI, WX], List::Nil),
        body,
    }
}

/// A vector by reference on the modifies line takes its value in and gives it back as a sequence, and `v[i] = x` writes one
/// element of the value after, decision 0145.
#[test]
fn an_element_write_sets_one_element_of_the_vector_after() {
    let vec = Ty::MutSeq(Scalar::I32);
    let set = Stmt::SetIndex(WV, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 6);
    let Model::Full(m) = translate_function(&write_at(one(set)), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.outs, List::Cons((WV, DTy::Seq(Scalar::I32)), Box::new(List::Nil)));
    let want = DStmt::SetOut(WV, DExpr::SetAt(Box::new(DExpr::Out(WV)), Box::new(DExpr::Var(WI)), Box::new(DExpr::Var(WX))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    // A read in code reads the value after.
    let read = Stmt::Local(WX + 1, Ty::I32, Expr::Index(b(Expr::Var(WV, vec)), b(Expr::Var(WI, Ty::U64))), 6);
    let Model::Full(m) = translate_function(&write_at(one(read)), &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DStmt::Local(WX + 1, DTy::Int32, DExpr::Index(Box::new(DExpr::Out(WV)), Box::new(DExpr::Var(WI))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
}

/// An element write to a read-only sequence parameter is a write to a parameter, decision 0145.
#[test]
fn an_element_write_to_a_read_only_sequence_is_refused() {
    let ro = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let f = Function {
        params: List::Cons((WV, ro), Box::new(List::Cons((WI, Ty::U64), Box::new(List::Cons((WX, Ty::I32), Box::new(List::Nil)))))),
        conds: List::Nil,
        ..write_at(one(Stmt::SetIndex(WV, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 6)))
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::WriteParam(WV, 6));
}

/// A call that passes a vector by reference on to a parameter that writes it has no rule yet, and the refusal says so, decision
/// 0147.
#[test]
fn a_vector_by_reference_passed_on_to_a_writer_is_refused() {
    let set = Stmt::SetIndex(WV, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 6);
    let all = fns(vec![Function { name: WX + 3, ..write_at(one(set)) }]);
    let vec = Ty::MutSeq(Scalar::I32);
    let args = List::Cons(b(Expr::Var(WV, vec)), Box::new(List::Cons(b(Expr::Var(WI, Ty::U64)), Box::new(List::Cons(b(Expr::Var(WX, Ty::I32)), Box::new(List::Nil))))));
    let caller = write_at(one(Stmt::Call(WX + 3, SAT_NAME, Box::new(args), 12)));
    assert_eq!(bare_refusal(translate_function(&caller, &all, &List::Nil)), Refusal::PassOn(WV, 12));
}

/// `v.push_back(x)` appends one element to the value after, decision 0148. On a read-only sequence it is a write to a parameter.
#[test]
fn push_back_appends_one_element_to_the_vector_after() {
    let push = Stmt::PushBack(WV, Expr::Var(WX, Ty::I32), 6);
    let Model::Full(m) = translate_function(&write_at(one(push)), &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DStmt::SetOut(WV, DExpr::Append(Box::new(DExpr::Out(WV)), Box::new(DExpr::Var(WX))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    let ro = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let f = Function {
        params: List::Cons((WV, ro), Box::new(List::Cons((WI, Ty::U64), Box::new(List::Cons((WX, Ty::I32), Box::new(List::Nil)))))),
        conds: List::Nil,
        ..write_at(one(Stmt::PushBack(WV, Expr::Var(WX, Ty::I32), 6)))
    };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::WriteParam(WV, 6));
}

const CV: u32 = 230;
const CK: u32 = 231;
const CX: u32 = 232;

/// `return std::count_if(v.begin(), v.end(), [k](int32_t x) { return x > k; });` is CountIf over the sequence with a Dafny
/// lambda, as an int64, decision 0149. The parameter of the lambda has the element type.
#[test]
fn count_if_with_a_lambda_is_count_if_of_the_prelude() {
    let seq = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let count = |xt: Ty| {
        let test = Expr::Bin(BinOp::Gt, b(Expr::Var(CX, Ty::I32)), b(Expr::Var(CK, Ty::I32)));
        Expr::CountIf(b(Expr::Var(CV, seq)), CX, xt, b(test))
    };
    let f = |xt: Ty| Function {
        name: SAT,
        line: 5,
        params: List::Cons((CV, seq), Box::new(List::Cons((CK, Ty::I32), Box::new(List::Nil)))),
        ret: Ty::I64,
        trusted: false,
        conds: List::Nil,
        body: one(Stmt::Return(count(xt), 6)),
    };
    let Model::Full(m) = translate_function(&f(Ty::I32), &List::Nil, &List::Nil) else { panic!("a full model") };
    let test = DExpr::Bin(BinOp::Gt, Box::new(DExpr::Var(CX)), Box::new(DExpr::Var(CK)));
    let want = DStmt::Return(DExpr::Conv(DTy::Int64, Box::new(DExpr::CountIf(Box::new(DExpr::Var(CV)), CX, DTy::Int32, Box::new(test)))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    assert_eq!(bare_refusal(translate_function(&f(Ty::I64), &List::Nil, &List::Nil)), Refusal::Syntax(6));
}

const DA: u32 = 240;
const DB: u32 = 241;
const DD: u32 = 242;

/// A requires line that says `std::isfinite(x)` of each name, joined by `&&`.
fn finite(ns: &[u32], line: u32, decl: &[u32]) -> Conds {
    let mut e = Expr::Finite(b(Expr::Name(ns[0])));
    for n in &ns[1..] {
        e = Expr::Bin(BinOp::And, b(e), b(Expr::Finite(b(Expr::Name(*n)))));
    }
    List::Cons((CondKind::Requires, e, line, names(decl)), Box::new(List::Nil))
}

/// `double larger(double a, double b) { if (a < b) { return b; } return a; }` with `requires std::isfinite(a) && std::isfinite(b)`.
fn larger(body: Stmts) -> Function {
    Function {
        name: SAT,
        line: 5,
        params: List::Cons((DA, Ty::F64), Box::new(List::Cons((DB, Ty::F64), Box::new(List::Nil)))),
        ret: Ty::F64,
        trusted: false,
        conds: finite(&[DA, DB], 4, &[DA, DB]),
        body,
    }
}

/// A double is a real, and a comparison of two doubles is the comparison of the reals, decision 0150. `std::isfinite` is true in
/// the model, which holds no NaN and no infinity.
#[test]
fn a_double_that_only_compares_is_a_real() {
    let test = Expr::Bin(BinOp::Lt, b(Expr::Var(DA, Ty::F64)), b(Expr::Var(DB, Ty::F64)));
    let body = List::Cons(
        Box::new(Stmt::If(test, Box::new(one(Stmt::Return(Expr::Var(DB, Ty::F64), 7))), Box::new(List::Nil), 6)),
        Box::new(one(Stmt::Return(Expr::Var(DA, Ty::F64), 9))),
    );
    let Model::Full(m) = translate_function(&larger(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.params, List::Cons((DA, DTy::Real), Box::new(List::Cons((DB, DTy::Real), Box::new(List::Nil)))));
    assert_eq!(m.ret, DTy::Real);
    let fin = DExpr::Bin(BinOp::And, Box::new(DExpr::Bool(true)), Box::new(DExpr::Bool(true)));
    assert_eq!(strip_conds(m.requires), List::Cons((fin, 0), Box::new(List::Nil)));
    let want = DStmt::If(
        DExpr::Bin(BinOp::Lt, Box::new(DExpr::Var(DA)), Box::new(DExpr::Var(DB))),
        Box::new(List::Cons((Box::new(DStmt::Return(DExpr::Var(DB))), 0), Box::new(List::Nil))),
        Box::new(List::Nil),
    );
    let List::Cons((first, _), _) = strip(m.body) else { panic!("a body") };
    assert_eq!(*first, want);
    // A literal is its digits over a power of ten, in code and in a contract.
    let Model::Full(m) = translate_function(&larger(one(Stmt::Return(Expr::RealLit(5, 1), 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::RealLit(5, 1))), 0), Box::new(List::Nil)));
    let ens = Expr::Bin(BinOp::Le, b(Expr::RealLit(0, 0)), b(Expr::Result));
    let f = Function { conds: List::Cons((CondKind::Ensures, ens, 4, names(&[DA, DB])), Box::new(finite(&[DA, DB], 3, &[DA, DB]))), ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::Bin(BinOp::Le, Box::new(DExpr::RealLit(0, 0)), Box::new(DExpr::Result)), 0), Box::new(List::Nil)));
}

/// A step that rounds and has no rule is refused in the core, so the model never makes exact real arithmetic of it, decision 0150.
/// Since decision 0154 the four operations are roundings of the model, so `%` and `++` are what is left.
#[test]
fn a_double_operation_that_rounds_is_refused() {
    for op in [BinOp::Rem] {
        let sum = Expr::Bin(op, b(Expr::Var(DA, Ty::F64)), b(Expr::Var(DB, Ty::F64)));
        assert_eq!(bare_refusal(translate_function(&larger(one(Stmt::Return(sum, 6))), &List::Nil, &List::Nil)), Refusal::Rounds(6), "{op:?}");
        // Through a parenthesis, a negation and a literal too.
        let sum = Expr::Bin(op, b(Expr::Paren(b(Expr::Neg(b(Expr::Var(DA, Ty::F64)))))), b(Expr::RealLit(1, 0)));
        assert_eq!(bare_refusal(translate_function(&larger(one(Stmt::Return(sum, 6))), &List::Nil, &List::Nil)), Refusal::Rounds(6), "{op:?}");
    }
    let body = List::Cons(
        Box::new(Stmt::Local(DD, Ty::F64, Expr::Var(DA, Ty::F64), 6)),
        Box::new(List::Cons(Box::new(Stmt::Step(DD, Ty::F64, true, 7)), Box::new(one(Stmt::Return(Expr::Var(DD, Ty::F64), 8))))),
    );
    assert_eq!(bare_refusal(translate_function(&larger(body), &List::Nil, &List::Nil)), Refusal::Rounds(7));
}

/// The model holds no NaN and no infinity, so each double parameter needs `std::isfinite` in a requires line, and a trusted
/// function that gives a double needs `std::isfinite(result)` in an ensures line, decision 0150. A field of type double has no
/// rule yet.
#[test]
fn a_double_needs_the_words_that_keep_nan_out() {
    let f = Function { conds: finite(&[DA], 4, &[DA, DB]), ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    assert_eq!(translate_function(&f, &List::Nil, &List::Nil), Model::Refused(Refusal::Finite(DB, 5)));
    let t = Function { params: List::Nil, conds: List::Nil, trusted: true, body: List::Nil, ..larger(List::Nil) };
    assert_eq!(translate_function(&t, &List::Nil, &List::Nil), Model::Refused(Refusal::FiniteResult(5)));
    let ens = Expr::Bin(BinOp::And, b(Expr::Finite(b(Expr::Result))), b(Expr::Bin(BinOp::Le, b(Expr::RealLit(0, 0)), b(Expr::Result))));
    let t = Function { conds: List::Cons((CondKind::Ensures, ens, 4, List::Nil), Box::new(List::Nil)), ..t };
    assert!(matches!(translate_function(&t, &List::Nil, &List::Nil), Model::Full(_)));
    let sd: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::F64), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    assert!(matches!(translate_structs(&sd), List::Cons(Err(_), _)));
}

/// `std::isfinite(x)` and a decimal with a point parse in a contract, decision 0150.
#[test]
fn isfinite_and_a_real_parse_in_a_contract() {
    let toks = vec![Tok::IsFinite, Tok::LParen, Tok::Ident(DA), Tok::RParen, Tok::Op(BinOp::And), Tok::Real(5, 1), Tok::Op(BinOp::Le), Tok::Ident(DA)];
    let want = Expr::Bin(BinOp::And, b(Expr::Finite(b(Expr::Name(DA)))), b(Expr::Bin(BinOp::Le, b(Expr::RealLit(5, 1)), b(Expr::Name(DA)))));
    assert_eq!(parse_contract(&toks, 4), Ok(want));
}

/// Each of the four operations on doubles is one rounding of the model, `fadd` to `fdiv`, decision 0154. A division of code is a
/// `Divide` with its type.
#[test]
fn a_double_operation_is_one_rounding_of_the_model() {
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        let e = Expr::Bin(op, b(Expr::Var(DA, Ty::F64)), b(Expr::Var(DB, Ty::F64)));
        let Model::Full(m) = translate_function(&larger(one(Stmt::Return(e, 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
        let want = DStmt::Return(DExpr::FOp(op, Box::new(DExpr::Var(DA)), Box::new(DExpr::Var(DB))));
        assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)), "{op:?}");
    }
    let e = Expr::Divide(BinOp::Div, b(Expr::Var(DA, Ty::F64)), b(Expr::Var(DB, Ty::F64)), Ty::F64);
    let Model::Full(m) = translate_function(&larger(one(Stmt::Return(e, 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DStmt::Return(DExpr::FOp(BinOp::Div, Box::new(DExpr::Var(DA)), Box::new(DExpr::Var(DB))));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    // In a contract, the absolute value and the words of a bound.
    let bound = Expr::Bin(BinOp::Le, b(Expr::Abs(b(Expr::Bin(BinOp::Mul, b(Expr::Name(DA)), b(Expr::Name(DB)))))), b(Expr::DblMax));
    let err = Expr::Bin(BinOp::Add, b(Expr::Bin(BinOp::Mul, b(Expr::Eps), b(Expr::Result))), b(Expr::Eta));
    let conds = List::Cons((CondKind::Requires, bound, 3, names(&[DA, DB])), Box::new(List::Cons((CondKind::Ensures, err, 4, names(&[DA, DB])), Box::new(finite(&[DA, DB], 2, &[DA, DB])))));
    let f = Function { conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let dbound = DExpr::Bin(BinOp::Le, Box::new(DExpr::Abs(Box::new(DExpr::Bin(BinOp::Mul, Box::new(DExpr::Var(DA)), Box::new(DExpr::Var(DB)))))), Box::new(DExpr::DblMax));
    let List::Cons((first, _), _) = strip_conds(m.requires) else { panic!("requires") };
    assert_eq!(first, dbound);
    let derr = DExpr::Bin(BinOp::Add, Box::new(DExpr::Bin(BinOp::Mul, Box::new(DExpr::Eps), Box::new(DExpr::Result))), Box::new(DExpr::Eta));
    assert_eq!(strip_conds(m.ensures), List::Cons((derr, 0), Box::new(List::Nil)));
}

/// `|e|` parses as the absolute value, decision 0154.
#[test]
fn the_absolute_value_parses_in_a_contract() {
    let toks = vec![Tok::Bar, Tok::Ident(DA), Tok::Op(BinOp::Mul), Tok::Ident(DB), Tok::Bar, Tok::Op(BinOp::Le), Tok::DblMax];
    let want = Expr::Bin(BinOp::Le, b(Expr::Abs(b(Expr::Bin(BinOp::Mul, b(Expr::Name(DA)), b(Expr::Name(DB)))))), b(Expr::DblMax));
    assert_eq!(parse_contract(&toks, 3), Ok(want));
}


/// `/` in a contract with a real operand is the real quotient, and on integers it keeps the division of C++, decision 0154.
#[test]
fn a_division_of_reals_in_a_contract_is_the_real_quotient() {
    let ens = Expr::Bin(BinOp::Le, b(Expr::Bin(BinOp::Div, b(Expr::Name(DA)), b(Expr::Name(DB)))), b(Expr::RealLit(1, 0)));
    let conds = List::Cons((CondKind::Ensures, ens, 4, names(&[DA, DB])), Box::new(finite(&[DA, DB], 3, &[DA, DB])));
    let f = Function { conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let q = DExpr::Bin(BinOp::Div, Box::new(DExpr::Var(DA)), Box::new(DExpr::Var(DB)));
    let want = DExpr::Bin(BinOp::Le, Box::new(q), Box::new(DExpr::RealLit(1, 0)));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

/// A requires line that the translator cannot read gets its own refusal, and the check of `std::isfinite` waits for it, decision
/// 0155. A conversion of a double to an integer is no double, so `%` on it is refused for the conversion.
#[test]
fn a_refusal_names_its_own_cause() {
    let bad = List::Cons((CondKind::Bad(Refusal::Syntax(4)), Expr::Int(0), 4, names(&[DA, DB])), Box::new(List::Nil));
    let f = Function { conds: bad, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Syntax(4));
    let cast = Expr::Cast(CastKind::Other(DD), b(Expr::Var(DA, Ty::F64)));
    // The plugin sends `%` of code as a Divide with its type, decision 0088.
    let rem = Expr::Divide(BinOp::Rem, b(cast), b(Expr::Lit(2, Ty::I32)), Ty::I32);
    let f = Function { ret: Ty::I32, ..larger(one(Stmt::Return(rem, 6))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Construct(DD, 6));
}


/// A double with no short decimal is `m / q` in code, with `q` a power of two, and the model writes the quotient of two
/// literals, which is exact, decision 0158. It is a double, so arithmetic on it rounds.
#[test]
fn an_exact_double_with_no_short_decimal_is_a_quotient_of_literals() {
    let q = 1u64 << 30;
    let lit = || DExpr::Bin(BinOp::Div, Box::new(DExpr::RealLit(1, 0)), Box::new(DExpr::RealLit(q, 0)));
    let Model::Full(m) = translate_function(&larger(one(Stmt::Return(Expr::Ratio(1, q), 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(lit())), 0), Box::new(List::Nil)));
    let e = Expr::Bin(BinOp::Mul, b(Expr::Var(DA, Ty::F64)), b(Expr::Ratio(1, q)));
    let Model::Full(m) = translate_function(&larger(one(Stmt::Return(e, 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DStmt::Return(DExpr::FOp(BinOp::Mul, Box::new(DExpr::Var(DA)), Box::new(lit())));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
}

/// An integer literal next to a real in a contract is that real, through a minus and parentheses too, decision 0158. An
/// operation on integers alone keeps its integers.
#[test]
fn an_integer_literal_next_to_a_real_is_a_real() {
    let real = |n| Box::new(DExpr::RealLit(n, 0));
    // `2 * eps <= DBL_MAX / 4`
    let ens = Expr::Bin(BinOp::Le, b(Expr::Bin(BinOp::Mul, b(Expr::Int(2)), b(Expr::Eps))), b(Expr::Bin(BinOp::Div, b(Expr::DblMax), b(Expr::Int(4)))));
    // `result >= (-1)`
    let low = Expr::Bin(BinOp::Ge, b(Expr::Result), b(Expr::Paren(b(Expr::Neg(b(Expr::Int(1)))))));
    // `1 / 2 + 3 <= 3`, integers alone.
    let ints = || Expr::Bin(BinOp::Le, b(Expr::Bin(BinOp::Add, b(Expr::Bin(BinOp::Div, b(Expr::Int(1)), b(Expr::Int(2)))), b(Expr::Int(3)))), b(Expr::Int(3)));
    let conds = List::Cons(
        (CondKind::Ensures, ens, 4, names(&[DA, DB])),
        Box::new(List::Cons((CondKind::Ensures, low, 5, names(&[DA, DB])), Box::new(List::Cons((CondKind::Ensures, ints(), 6, names(&[DA, DB])), Box::new(finite(&[DA, DB], 3, &[DA, DB])))))),
    );
    let f = Function { conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 8))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let dens = DExpr::Bin(BinOp::Le, Box::new(DExpr::Bin(BinOp::Mul, real(2), Box::new(DExpr::Eps))), Box::new(DExpr::Bin(BinOp::Div, Box::new(DExpr::DblMax), real(4))));
    let dlow = DExpr::Bin(BinOp::Ge, Box::new(DExpr::Result), Box::new(DExpr::Neg(real(1))));
    let List::Cons((first, _), rest) = strip_conds(m.ensures) else { panic!("ensures") };
    assert_eq!(first, dens);
    let List::Cons((second, _), rest) = *rest else { panic!("ensures") };
    assert_eq!(second, dlow);
    // The line of integers is the one that it is with no real in the function.
    let List::Cons((third, _), _) = *rest else { panic!("ensures") };
    let f = Function { conds: List::Cons((CondKind::Ensures, ints(), 6, names(&[DA, DB])), Box::new(finite(&[DA, DB], 3, &[DA, DB]))), ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 8))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((alone, _), _) = strip_conds(m.ensures) else { panic!("ensures") };
    assert_eq!(third, alone);
    assert!(!format!("{alone:?}").contains("RealLit"), "{alone:?}");
}

/// A chain is two comparisons, decision 0064, so an integer literal in a chain next to a real is a real too, decision 0158. A chain
/// on an integer keeps its integers.
#[test]
fn an_integer_literal_in_a_chain_next_to_a_real_is_a_real() {
    const DN: u32 = 9911;
    let chain = |n| Expr::Chain(BinOp::Le, BinOp::Le, b(Expr::Int(0)), b(Expr::Name(n)), b(Expr::Int(1)));
    let params = List::Cons((DA, Ty::F64), Box::new(List::Cons((DN, Ty::I32), Box::new(List::Nil))));
    let conds = List::Cons(
        (CondKind::Requires, chain(DA), 3, names(&[DA, DN])),
        Box::new(List::Cons((CondKind::Requires, chain(DN), 4, names(&[DA, DN])), Box::new(finite(&[DA], 2, &[DA, DN])))),
    );
    let f = Function { params, conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((first, _), rest) = strip_conds(m.requires) else { panic!("requires") };
    assert_eq!(first, DExpr::Chain(BinOp::Le, BinOp::Le, Box::new(DExpr::RealLit(0, 0)), Box::new(DExpr::Var(DA)), Box::new(DExpr::RealLit(1, 0))));
    let List::Cons((second, _), _) = *rest else { panic!("requires") };
    let int = DExpr::Chain(BinOp::Le, BinOp::Le, Box::new(DExpr::Lit(0)), Box::new(DExpr::AsInt(Box::new(DExpr::Var(DN)))), Box::new(DExpr::Lit(1)));
    assert_eq!(second, int);
}

/// A conversion of an integer to a double is `fint` of the double model, which is exact up to 2^53, decision 0159. A conversion of
/// a double to an integer, and of a bool to a double, stay refused.
#[test]
fn an_integer_converts_to_a_double_with_fint() {
    const DN: u32 = 9912;
    let f = |e| Function { params: List::Cons((DN, Ty::I64), Box::new(List::Nil)), conds: List::Nil, ..larger(one(Stmt::Return(e, 6))) };
    let Model::Full(m) = translate_function(&f(Expr::Cast(CastKind::Integral(Ty::I64, Ty::F64), b(Expr::Var(DN, Ty::I64)))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::FromInt(Box::new(DExpr::Var(DN))))), 0), Box::new(List::Nil)));
    let back = Function { ret: Ty::I64, ..larger(one(Stmt::Return(Expr::Cast(CastKind::Integral(Ty::F64, Ty::I64), b(Expr::Var(DA, Ty::F64))), 6))) };
    assert_eq!(bare_refusal(translate_function(&back, &List::Nil, &List::Nil)), Refusal::Convert(6));
    assert_eq!(bare_refusal(translate_function(&f(Expr::Cast(CastKind::Integral(Ty::Bool, Ty::F64), b(Expr::Bool(true)))), &List::Nil, &List::Nil)), Refusal::Convert(6));
}

/// In a contract, `|e|` of an integer is the absolute value of the integer, and an integer name next to a real is that integer as
/// a real, decision 0159. An operation on integers alone stays an integer.
#[test]
fn a_contract_reads_an_integer_next_to_a_real_as_a_real() {
    const DN: u32 = 9913;
    let params = || List::Cons((DA, Ty::F64), Box::new(List::Cons((DN, Ty::I32), Box::new(List::Nil))));
    let n = || DExpr::AsInt(Box::new(DExpr::Var(DN)));
    // `|n| <= 3`, `n <= a` and `n * 2 <= a`
    let iabs = Expr::Bin(BinOp::Le, b(Expr::Abs(b(Expr::Name(DN)))), b(Expr::Int(3)));
    let near = Expr::Bin(BinOp::Le, b(Expr::Name(DN)), b(Expr::Name(DA)));
    let op = Expr::Bin(BinOp::Le, b(Expr::Bin(BinOp::Mul, b(Expr::Name(DN)), b(Expr::Int(2)))), b(Expr::Name(DA)));
    let conds = List::Cons(
        (CondKind::Requires, iabs, 3, names(&[DA, DN])),
        Box::new(List::Cons((CondKind::Requires, near, 4, names(&[DA, DN])), Box::new(List::Cons((CondKind::Requires, op, 5, names(&[DA, DN])), Box::new(finite(&[DA], 2, &[DA, DN])))))),
    );
    let f = Function { params: params(), conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 7))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((first, _), rest) = strip_conds(m.requires) else { panic!("requires") };
    assert_eq!(first, DExpr::Bin(BinOp::Le, Box::new(DExpr::IntAbs(Box::new(n()))), Box::new(DExpr::Lit(3))));
    let List::Cons((second, _), rest) = *rest else { panic!("requires") };
    assert_eq!(second, DExpr::Bin(BinOp::Le, Box::new(DExpr::Conv(DTy::Real, Box::new(n()))), Box::new(DExpr::Var(DA))));
    let List::Cons((third, _), _) = *rest else { panic!("requires") };
    assert!(!format!("{third:?}").contains("Conv(Real"), "{third:?}");
}

/// A name that a `forall` binds is an exact integer, so next to a real it is that integer as a real, decision 0159.
#[test]
fn a_bound_name_next_to_a_real_is_a_real() {
    const DI: u32 = 9914;
    let all = Expr::Forall(DI, b(Expr::Bin(BinOp::Le, b(Expr::Name(DI)), b(Expr::Name(DA)))));
    let conds = List::Cons((CondKind::Requires, all, 3, names(&[DA, DB])), Box::new(finite(&[DA, DB], 2, &[DA, DB])));
    let f = Function { conds, ..larger(one(Stmt::Return(Expr::Var(DA, Ty::F64), 6))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((first, _), _) = strip_conds(m.requires) else { panic!("requires") };
    let want = DExpr::Forall(DI, Box::new(DExpr::Bin(BinOp::Le, Box::new(DExpr::Conv(DTy::Real, Box::new(DExpr::Bound(DI)))), Box::new(DExpr::Var(DA)))));
    assert_eq!(first, want);
}

const LX: u32 = 250;

/// `int32_t f(std::vector<int32_t>& v, size_t i, int32_t x)` with `modifies v`, whose body starts with `std::vector<int32_t> copy = v;`,
/// decision 0160.
fn with_copy(rest: Stmts) -> Function {
    let seq = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let copy = Stmt::Local(LX, Ty::Vec(Scalar::I32), Expr::Copy(b(Expr::Var(WV, Ty::MutSeq(Scalar::I32))), seq, seq), 6);
    Function { ret: Ty::I32, ..write_at(List::Cons(Box::new(copy), Box::new(rest))) }
}

/// A local vector is a copy of a vector in scope, decision 0160. A write to the vector after the copy leaves the copy as it was,
/// and a write to the copy is a new value of the local.
#[test]
fn a_local_vector_is_a_copy() {
    let local = Ty::Vec(Scalar::I32);
    let body = List::Cons(
        Box::new(Stmt::SetIndex(WV, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 7)),
        Box::new(List::Cons(
            Box::new(Stmt::SetIndex(LX, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 8)),
            Box::new(List::Cons(
                Box::new(Stmt::PushBack(LX, Expr::Var(WX, Ty::I32), 9)),
                Box::new(one(Stmt::Return(Expr::Index(b(Expr::Var(LX, local)), b(Expr::Var(WI, Ty::U64))), 10))),
            )),
        )),
    );
    let Model::Full(m) = translate_function(&with_copy(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let x = || Box::new(DExpr::Var(LX));
    let i = || Box::new(DExpr::Var(WI));
    let e = || Box::new(DExpr::Var(WX));
    let want = [
        DStmt::Local(LX, DTy::Seq(Scalar::I32), DExpr::Out(WV)),
        DStmt::SetOut(WV, DExpr::SetAt(Box::new(DExpr::Out(WV)), i(), e())),
        DStmt::Assign(LX, DExpr::SetAt(x(), i(), e())),
        DStmt::Assign(LX, DExpr::Append(x(), e())),
        DStmt::Return(DExpr::Index(x(), i())),
    ];
    let mut body = strip(m.body);
    for w in want {
        let List::Cons((s, _), rest) = body else { panic!("a statement for {w:?}") };
        assert_eq!(*s, w);
        body = *rest;
    }
    assert_eq!(body, List::Nil);
}

/// A local vector has a rule only as a copy of a vector in scope of the same element, decision 0160. A local span is a view, and a
/// call that passes a local vector by reference has no rule yet.
#[test]
fn a_local_vector_that_is_no_copy_is_refused() {
    let seq = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let local = |t, e| Function { ret: Ty::I32, ..write_at(List::Cons(Box::new(Stmt::Local(LX, t, e, 6)), Box::new(one(Stmt::Return(Expr::Var(WX, Ty::I32), 7))))) };
    let copy = || Expr::Copy(b(Expr::Var(WV, Ty::MutSeq(Scalar::I32))), seq, seq);
    let refused = |f: Function| bare_refusal(translate_function(&f, &List::Nil, &List::Nil));
    // Not from a copy.
    assert_eq!(refused(local(Ty::Vec(Scalar::I32), Expr::Var(WV, Ty::MutSeq(Scalar::I32)))), Refusal::VecLocal(6));
    // A copy of a sequence of another element.
    let bytes = Ty::Seq(Scalar::U8, Extent::Dynamic);
    let f = local(Ty::Vec(Scalar::I32), Expr::Copy(b(Expr::Var(WI, bytes)), bytes, bytes));
    assert_eq!(refused(f), Refusal::VecLocal(6));
    // A vector of bool, and of a struct.
    assert_eq!(refused(local(Ty::Vec(Scalar::Bool), copy())), Refusal::Element(6));
    assert_eq!(refused(local(Ty::Vec(Scalar::Struct(POINT)), copy())), Refusal::VecLocal(6));
    // A copy of a vector of a struct that holds a sequence, decisions 0076 and 0163.
    let points = Ty::Seq(Scalar::Struct(POINT), Extent::Dynamic);
    let holds: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let f = local(Ty::Vec(Scalar::Struct(POINT)), Expr::Copy(b(Expr::Var(WI, points)), points, points));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &holds)), Refusal::HoldsSeq(6));
    // A span is a view.
    assert_eq!(refused(local(seq, copy())), Refusal::SeqParam(6));
    // A call that passes the local by reference to a writer writes it back to the local, decision 0170.
    let set = Stmt::SetIndex(WV, Expr::Var(WI, Ty::U64), Expr::Var(WX, Ty::I32), 6);
    let all = fns(vec![Function { name: WX + 3, ..write_at(one(set)) }]);
    let args = List::Cons(b(Expr::Var(LX, Ty::Vec(Scalar::I32))), Box::new(List::Cons(b(Expr::Var(WI, Ty::U64)), Box::new(List::Cons(b(Expr::Var(WX, Ty::I32)), Box::new(List::Nil))))));
    let caller = with_copy(List::Cons(Box::new(Stmt::Call(WX + 3, SAT_NAME, Box::new(args), 12)), Box::new(one(Stmt::Return(Expr::Var(WX, Ty::I32), 13)))));
    let Model::Full(m) = translate_function(&caller, &all, &List::Nil) else { panic!("a full model of the caller") };
    assert!(format!("{:?}", m.body).contains(&format!("Update(Cons(Local({LX}), Nil)")), "{m:?}");
}

/// `std::sort(v.begin(), v.end())` of a local vector or of a vector by reference is StdSort with `<` on its elements, decision
/// 0161. A sort of a read-only sequence is a write to a parameter, and a sort of a vector of a struct needs a comparator.
#[test]
fn a_sort_of_a_vector_is_std_sort() {
    let body = List::Cons(Box::new(Stmt::Sort(LX, 7)), Box::new(one(Stmt::Return(Expr::Index(b(Expr::Var(LX, Ty::Vec(Scalar::I32))), b(Expr::Var(WI, Ty::U64))), 8))));
    let Model::Full(m) = translate_function(&with_copy(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("the copy") };
    let List::Cons((sort, _), _) = *rest else { panic!("the sort") };
    assert_eq!(*sort, DStmt::Sort(Box::new(DExpr::Var(LX)), DTy::Int32));
    // A vector by reference sorts its value after.
    let Model::Full(m) = translate_function(&write_at(one(Stmt::Sort(WV, 6))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Sort(Box::new(DExpr::Out(WV)), DTy::Int32)), 0), Box::new(List::Nil)));
    // A read-only sequence.
    let ro = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let f = Function { params: List::Cons((WV, ro), Box::new(List::Nil)), conds: List::Nil, ..write_at(one(Stmt::Sort(WV, 6))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::WriteParam(WV, 6));
    // A vector of a struct.
    let points = Ty::MutSeq(Scalar::Struct(POINT));
    let f = Function { params: List::Cons((WV, points), Box::new(List::Nil)), conds: modifies(&[WV], &[WV], List::Nil), ..write_at(one(Stmt::Sort(WV, 6))) };
    let sd: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &sd)), Refusal::SortForm(6));
    // A name that is no vector is another form.
    let f = write_at(one(Stmt::Sort(LX, 6)));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::SortForm(6));
}

const CA: u32 = 260;
const CB: u32 = 261;

/// `std::sort(v.begin(), v.end(), [](T a, T b) { return e; })` is StdSort with the lambda as its comparator, decision 0162. Each
/// parameter has the element type, and the test holds no call. A vector of a struct by reference sorts by a field.
#[test]
fn a_sort_with_a_comparator_is_std_sort_with_the_lambda() {
    let down = || Expr::Bin(BinOp::Gt, b(Expr::Var(CA, Ty::I32)), b(Expr::Var(CB, Ty::I32)));
    let body = List::Cons(Box::new(Stmt::SortBy(LX, CA, CB, Ty::I32, down(), 7)), Box::new(one(Stmt::Return(Expr::Var(WX, Ty::I32), 8))));
    let Model::Full(m) = translate_function(&with_copy(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("the copy") };
    let List::Cons((sort, _), _) = *rest else { panic!("the sort") };
    let want = DStmt::SortBy(Box::new(DExpr::Var(LX)), CA, CB, DTy::Int32, Box::new(translate_code(&down(), 7).unwrap()));
    assert_eq!(*sort, want);
    // A vector of a struct by reference, by a field.
    let key = || Expr::Bin(BinOp::Lt, b(Expr::Field(b(Expr::Var(CA, Ty::Struct(POINT))), FX)), b(Expr::Field(b(Expr::Var(CB, Ty::Struct(POINT))), FX)));
    let points = Ty::MutSeq(Scalar::Struct(POINT));
    let sd: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let by_key = |t, e| Function {
        params: List::Cons((WV, points), Box::new(List::Nil)),
        conds: modifies(&[WV], &[WV], List::Nil),
        ..write_at(one(Stmt::SortBy(WV, CA, CB, t, e, 6)))
    };
    let Model::Full(m) = translate_function(&by_key(Ty::Struct(POINT), key()), &List::Nil, &sd) else { panic!("a full model") };
    let want = DStmt::SortBy(Box::new(DExpr::Out(WV)), CA, CB, DTy::Struct(POINT), Box::new(translate_code(&key(), 6).unwrap()));
    assert_eq!(strip(m.body), List::Cons((Box::new(want), 0), Box::new(List::Nil)));
    // A parameter of another type is another form.
    assert_eq!(bare_refusal(translate_function(&by_key(Ty::I32, key()), &List::Nil, &sd)), Refusal::SortForm(6));
    // A read-only sequence is a parameter that the sort writes.
    let ro = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let f = Function { params: List::Cons((WV, ro), Box::new(List::Nil)), conds: List::Nil, ..write_at(one(Stmt::SortBy(WV, CA, CB, Ty::I32, down(), 6))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::WriteParam(WV, 6));
    // A test with a call is refused as a call out of place.
    let call = Expr::Call(SAT, SAT_NAME, Box::new(List::Nil), 6);
    let f = with_copy(List::Cons(Box::new(Stmt::SortBy(LX, CA, CB, Ty::I32, call, 7)), Box::new(one(Stmt::Return(Expr::Var(WX, Ty::I32), 8)))));
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::Place(6));
}

/// A vector of a struct is a sequence of its datatype: a local copy, decision 0163. A function gives a vector as a sequence, a
/// return of a local vector gives its value, and a local can take the vector that a call gives.
#[test]
fn a_vector_of_a_struct_and_a_vector_as_a_result() {
    let points = Ty::Seq(Scalar::Struct(POINT), Extent::Dynamic);
    let sd: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::I32), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let copy = Stmt::Local(LX, Ty::Vec(Scalar::Struct(POINT)), Expr::Copy(b(Expr::Var(WV, points)), points, points), 6);
    let give = |body| Function {
        params: List::Cons((WV, points), Box::new(List::Nil)),
        ret: Ty::Vec(Scalar::Struct(POINT)),
        conds: List::Nil,
        ..write_at(body)
    };
    let f = give(List::Cons(Box::new(copy), Box::new(one(Stmt::Return(Expr::Var(LX, Ty::Vec(Scalar::Struct(POINT))), 7)))));
    let Model::Full(m) = translate_function(&f, &List::Nil, &sd) else { panic!("a full model") };
    assert_eq!(m.ret, DTy::Seq(Scalar::Struct(POINT)));
    let want = List::Cons(
        (Box::new(DStmt::Local(LX, DTy::Seq(Scalar::Struct(POINT)), DExpr::Var(WV))), 0),
        Box::new(List::Cons((Box::new(DStmt::Return(DExpr::Var(LX))), 0), Box::new(List::Nil))),
    );
    assert_eq!(strip(m.body), want);
    // A contract reads the size of the result.
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Size(b(Expr::Result))), b(Expr::Size(b(Expr::Name(WV)))));
    let f = Function { conds: List::Cons((CondKind::Ensures, ens, 4, names(&[WV])), Box::new(List::Nil)), ..f };
    let Model::Full(m) = translate_function(&f, &List::Nil, &sd) else { panic!("a full model") };
    let List::Cons((e, _), _) = strip_conds(m.ensures) else { panic!("ensures") };
    assert!(format!("{e:?}").contains("Len(Result)"), "{e:?}");
    // A local from a call that gives a vector.
    let callee = Function { name: WX + 5, ..give(one(Stmt::Return(Expr::Var(WV, points), 7))) };
    let all = fns(vec![callee]);
    let args = List::Cons(b(Expr::Var(WV, points)), Box::new(List::Nil));
    let call = Stmt::Local(LX, Ty::Vec(Scalar::Struct(POINT)), Expr::Call(WX + 5, SAT_NAME, Box::new(args), 6), 6);
    let caller = Function { ret: Ty::I32, ..give(List::Cons(Box::new(call), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 7))))) };
    let Model::Full(m) = translate_function(&caller, &all, &sd) else { panic!("a full model") };
    let List::Cons((first, _), _) = strip(m.body) else { panic!("a body") };
    assert!(matches!(*first, DStmt::LocalCall(LX, DTy::Seq(Scalar::Struct(POINT)), _, _)), "{first:?}");
}

/// A vector by reference of a struct that holds a sequence is refused, and a local vector that copies a name not in scope is no
/// copy of a vector in scope, decision 0164.
#[test]
fn a_vector_of_a_struct_that_holds_a_sequence_and_a_copy_of_no_name_are_refused() {
    let holds: Structs = List::Cons((POINT, (3, List::Cons((FX, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let f = Function {
        params: List::Cons((WV, Ty::MutSeq(Scalar::Struct(POINT))), Box::new(List::Nil)),
        conds: modifies(&[WV], &[WV], List::Nil),
        ..write_at(List::Nil)
    };
    // The signature is refused, so the function has no model at all.
    assert_eq!(translate_function(&f, &List::Nil, &holds), Model::Refused(Refusal::HoldsSeq(f.line)));
    let seq = Ty::Seq(Scalar::I32, Extent::Dynamic);
    let own = Stmt::Local(LX, Ty::Vec(Scalar::I32), Expr::Copy(b(Expr::Var(LX, Ty::Vec(Scalar::I32))), seq, seq), 6);
    let f = Function { ret: Ty::I32, ..write_at(List::Cons(Box::new(own), Box::new(one(Stmt::Return(Expr::Var(WX, Ty::I32), 7))))) };
    assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &List::Nil)), Refusal::VecLocal(6));
}

const SHAPE: u32 = 300;
const SQUARE: u32 = 301;
const CORNERS: u32 = 302;
const BKEY: u32 = 303;
const DKEY: u32 = 304;
const VX: u32 = 305;
const VY: u32 = 306;
const BKEY2: u32 = 307;

/// `virtual int32_t corners() const = 0;` of the interface Shape, with `ensures result >= 3`, decision 0165.
fn base_corners(params: Params, conds: Conds) -> Function {
    Function { name: BKEY, line: 9, params: List::Cons((THIS, Ty::Iface(SHAPE)), Box::new(params)), ret: Ty::I32, trusted: true, conds, body: List::Nil }
}

/// `int32_t corners() const override { return 4; }` of the final class Square.
fn derived_corners(params: Params, conds: Conds) -> Function {
    Function { name: DKEY, line: 15, params: List::Cons((THIS, Ty::This(SQUARE)), Box::new(params)), ret: Ty::I32, trusted: false, conds, body: one(Stmt::Return(Expr::Lit(4, Ty::I32), 15)) }
}

fn at_least_three() -> Conds {
    List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Ge, b(Expr::Result), b(Expr::Int(3))), 8, names(&[THIS])), Box::new(List::Nil))
}

/// The interface Shape, with no field, and the final class Square over it.
fn shapes(square_members: Members) -> Structs {
    let shape = (SHAPE, (5, List::Nil, List::Cons((CORNERS, (BKEY, None)), Box::new(List::Nil))));
    List::Cons(shape, Box::new(List::Cons((SQUARE, (12, List::Nil, square_members)), Box::new(List::Nil))))
}

fn corners_member() -> Members {
    List::Cons((CORNERS, (DKEY, None)), Box::new(List::Nil))
}

/// An interface is a type of the model with no value that it can see. It is a parameter only, decision 0165.
#[test]
fn an_interface_is_a_type_of_the_model_and_a_parameter_only() {
    assert_eq!(translate_ty(Ty::Iface(SHAPE), 3), Ok(DTy::Iface(SHAPE)));
    assert_eq!(translate_value_ty(Ty::Iface(SHAPE), 3, &shapes(corners_member())), Err(Refusal::Syntax(3)));
    // A pure virtual function is a trusted function of the interface: its contract with no body.
    let Model::Full(m) = translate_function(&base_corners(List::Nil, at_least_three()), &List::Nil, &shapes(corners_member())) else { panic!("a full model") };
    assert!(m.trusted && m.body == List::Nil, "{m:?}");
    assert_eq!(m.params, List::Cons((THIS, DTy::Iface(SHAPE)), Box::new(List::Nil)));
}

/// Each override of a final class over an interface has its check: the contract of the base function read on the override, with
/// the parameters of the override, and the requires lines of the override itself, decision 0165.
#[test]
fn each_override_is_checked_against_the_contract_of_the_interface() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let all = fns(vec![base_corners(List::Nil, at_least_three()), derived_corners(List::Nil, List::Nil)]);
    let Model::Full(base) = translate_function(&base_corners(List::Nil, at_least_three()), &List::Nil, &shapes(corners_member())) else { panic!("a full model") };
    let List::Cons(Ok(up), rest) = translate_overrides(&bases, &all, &shapes(corners_member())) else { panic!("one upcast") };
    assert_eq!(*rest, List::Nil);
    assert_eq!((up.derived, up.base), (SQUARE, SHAPE));
    let List::Cons(o, more) = up.overrides else { panic!("one override") };
    assert_eq!(*more, List::Nil);
    assert_eq!((o.base, o.derived, o.ret), (BKEY, DKEY, DTy::Int32));
    assert_eq!(o.params, List::Nil);
    assert_eq!(strip_conds(o.requires), List::Nil);
    // The ensures line of the interface, with no line that links the method to its function, decision 0166.
    let List::Cons(first, _) = base.ensures else { panic!("the ensures line of the interface") };
    assert_eq!(strip_conds(o.ensures), strip_conds(List::Cons(first, Box::new(List::Nil))));
    assert_eq!(o.own, List::Nil);
}

/// The parameters of the override take the place of those of the base function, by their place, and the requires lines of the
/// override are part of the check, decision 0165.
#[test]
fn an_override_check_reads_the_parameters_of_the_override() {
    let base_conds = List::Cons(
        (CondKind::Requires, Expr::Bin(BinOp::Le, b(Expr::Int(0)), b(Expr::Name(VX))), 7, names(&[THIS, VX])),
        Box::new(List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Ge, b(Expr::Result), b(Expr::Name(VX))), 8, names(&[THIS, VX])), Box::new(List::Nil))),
    );
    let own = List::Cons((CondKind::Requires, Expr::Bin(BinOp::Lt, b(Expr::Name(VY)), b(Expr::Int(100))), 14, names(&[THIS, VY])), Box::new(List::Nil));
    let base = base_corners(List::Cons((VX, Ty::I32), Box::new(List::Nil)), base_conds);
    let derived = derived_corners(List::Cons((VY, Ty::I32), Box::new(List::Nil)), own);
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let List::Cons(Ok(up), _) = translate_overrides(&bases, &fns(vec![base, derived]), &shapes(corners_member())) else { panic!("one upcast") };
    let List::Cons(o, _) = up.overrides else { panic!("one override") };
    assert_eq!(o.params, List::Cons((VY, DTy::Int32), Box::new(List::Nil)));
    let as_int = |n: u32| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    assert_eq!(o.requires, List::Cons((DExpr::Bin(BinOp::Le, Box::new(DExpr::Lit(0)), as_int(VY)), 7), Box::new(List::Nil)));
    assert_eq!(o.ensures, List::Cons((DExpr::Bin(BinOp::Ge, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), as_int(VY)), 8), Box::new(List::Nil)));
    assert_eq!(o.own, List::Cons((DExpr::Bin(BinOp::Lt, as_int(VY), Box::new(DExpr::Lit(100))), 14), Box::new(List::Nil)));
}

/// A class with no override of a virtual function of its base, an override with other parameters or another result, an override
/// with no function in the model, and a class that is not final are refused at the line of the class. An interface with two virtual
/// functions of one name is refused at its own line, decision 0165.
#[test]
fn a_class_with_no_override_or_an_override_that_cannot_be_checked_is_refused() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let base = || base_corners(List::Nil, at_least_three());
    // No member of the name.
    let all = fns(vec![base(), derived_corners(List::Nil, List::Nil)]);
    assert_eq!(translate_overrides(&bases, &all, &shapes(List::Nil)), List::Cons(Err(Refusal::NoOverride(SQUARE, SHAPE, CORNERS, 12)), Box::new(List::Nil)));
    // Other parameters.
    let all = fns(vec![base(), derived_corners(List::Cons((VY, Ty::I32), Box::new(List::Nil)), List::Nil)]);
    assert_eq!(translate_overrides(&bases, &all, &shapes(corners_member())), List::Cons(Err(Refusal::NoOverride(SQUARE, SHAPE, CORNERS, 12)), Box::new(List::Nil)));
    // The same count of parameters, of another type.
    let all = fns(vec![base_corners(List::Cons((VX, Ty::I32), Box::new(List::Nil)), List::Nil), derived_corners(List::Cons((VY, Ty::I64), Box::new(List::Nil)), List::Nil)]);
    assert_eq!(translate_overrides(&bases, &all, &shapes(corners_member())), List::Cons(Err(Refusal::NoOverride(SQUARE, SHAPE, CORNERS, 12)), Box::new(List::Nil)));
    // Another result.
    let all = fns(vec![base(), Function { ret: Ty::I64, body: one(Stmt::Return(Expr::Lit(4, Ty::I64), 15)), ..derived_corners(List::Nil, List::Nil) }]);
    assert_eq!(translate_overrides(&bases, &all, &shapes(corners_member())), List::Cons(Err(Refusal::NoOverride(SQUARE, SHAPE, CORNERS, 12)), Box::new(List::Nil)));
    // A trusted override has no function in the model.
    let all = fns(vec![base(), Function { trusted: true, body: List::Nil, ..derived_corners(List::Nil, List::Nil) }]);
    assert_eq!(translate_overrides(&bases, &all, &shapes(corners_member())), List::Cons(Err(Refusal::Unchecked(SQUARE, SHAPE, CORNERS, 12)), Box::new(List::Nil)));
    // Two virtual functions of one name. The plugin leaves the name out of the members of the interface, so the core refuses the
    // interface.
    let all = fns(vec![base(), Function { name: BKEY2, ..base() }, derived_corners(List::Nil, List::Nil)]);
    let sd = List::Cons((SHAPE, (5, List::Nil, List::Nil)), Box::new(List::Cons((SQUARE, (12, List::Nil, corners_member())), Box::new(List::Nil))));
    assert_eq!(translate_overrides(&bases, &all, &sd), List::Cons(Err(Refusal::Overload(SHAPE, 5)), Box::new(List::Nil)));
    // A class over an interface that is not final.
    let open = List::Cons((SQUARE, (names(&[SHAPE]), false)), Box::new(List::Nil));
    let all = fns(vec![base(), derived_corners(List::Nil, List::Nil)]);
    assert_eq!(translate_overrides(&open, &all, &shapes(corners_member())), List::Cons(Err(Refusal::NotFinal(SQUARE, 12)), Box::new(List::Nil)));
}

/// A free function of `const Shape&` is no virtual function of the interface, so it does not make the interface look overloaded,
/// decision 0165.
#[test]
fn a_free_function_of_an_interface_is_no_virtual_function_of_it() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let count = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil)),
        trusted: false,
        conds: List::Nil,
        body: one(Stmt::Return(Expr::Lit(3, Ty::I32), 21)),
        ..base_corners(List::Nil, List::Nil)
    };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), count, derived_corners(List::Nil, List::Nil)]);
    assert!(matches!(translate_overrides(&bases, &all, &shapes(corners_member())), List::Cons(Ok(_), ref rest) if **rest == List::Nil));
    assert_eq!(translate_ty(Ty::IfaceRef(SHAPE), 3), Ok(DTy::Iface(SHAPE)));
    assert_eq!(translate_value_ty(Ty::IfaceRef(SHAPE), 3, &shapes(corners_member())), Err(Refusal::Syntax(3)));
}

const COLORED: u32 = 308;
const RED: u32 = 309;
const RKEY: u32 = 310;
const DRED: u32 = 311;

/// A class over two interfaces has a check for each, in the order of its bases, decision 0165.
#[test]
fn a_class_over_two_interfaces_has_a_check_for_each() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE, COLORED]), true)), Box::new(List::Nil));
    let base_red = Function { name: RKEY, line: 30, params: List::Cons((THIS, Ty::Iface(COLORED)), Box::new(List::Nil)), ..base_corners(List::Nil, List::Nil) };
    let derived_red = Function { name: DRED, line: 18, ..derived_corners(List::Nil, List::Nil) };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), base_red, derived_corners(List::Nil, List::Nil), derived_red]);
    let colored = (COLORED, (28, List::Nil, List::Cons((RED, (RKEY, None)), Box::new(List::Nil))));
    let square = List::Cons((CORNERS, (DKEY, None)), Box::new(List::Cons((RED, (DRED, None)), Box::new(List::Nil))));
    let sd = List::Cons(colored, Box::new(shapes(square)));
    let List::Cons(Ok(first), rest) = translate_overrides(&bases, &all, &sd) else { panic!("an upcast to Shape") };
    let List::Cons(Ok(second), rest) = *rest else { panic!("an upcast to Colored") };
    assert_eq!(*rest, List::Nil);
    assert_eq!((first.derived, first.base, second.derived, second.base), (SQUARE, SHAPE, SQUARE, COLORED));
    let List::Cons(o, _) = second.overrides else { panic!("one override") };
    assert_eq!((o.base, o.derived), (RKEY, DRED));
}

const IVALID: u32 = 312;
const IVKEY: u32 = 313;

/// `virtual bool valid() const = 0;` of the interface Shape, with no contract.
fn base_valid() -> Function {
    Function { name: IVKEY, line: 6, ret: Ty::Bool, ..base_corners(List::Nil, List::Nil) }
}

/// The interface Shape with its members in the order given, and the final class Square with none.
fn shape_of(members: &[(u32, u32)]) -> Structs {
    let ms = members.iter().rev().fold(List::Nil, |rest, (n, k)| List::Cons((*n, (*k, None)), Box::new(rest)));
    List::Cons((SHAPE, (5, List::Nil, ms)), Box::new(List::Cons((SQUARE, (12, List::Nil, List::Nil)), Box::new(List::Nil))))
}

/// The method of a pure virtual function also says that its result is the value of its function, decision 0166.
#[test]
fn a_pure_virtual_function_is_a_function_of_the_model() {
    let all = fns(vec![base_corners(List::Nil, at_least_three())]);
    let List::Cons(Model::Full(m), _) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model") };
    let link = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(BKEY, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))))));
    assert!(m.trusted && m.body == List::Nil, "{m:?}");
    let List::Cons(_, rest) = m.ensures else { panic!("the ensures line of the interface") };
    assert_eq!(*rest, List::Cons((link, 9), Box::new(List::Nil)));
}

/// A contract of a virtual function calls a virtual function of its interface on its object when that function comes first.
/// A function that comes later is refused at the line of the contract, decision 0166.
#[test]
fn a_contract_of_an_interface_calls_a_virtual_function_above_it() {
    let req = List::Cons((CondKind::Requires, Expr::Apply(IVALID, Box::new(List::Nil)), 7, names(&[THIS])), Box::new(List::Nil));
    let all = fns(vec![base_valid(), base_corners(List::Nil, req)]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(IVALID, IVKEY), (CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of corners") };
    let on_this = DExpr::FCall(IVKEY, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))));
    assert_eq!(m.requires, List::Cons((on_this, 7), Box::new(List::Nil)));
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY), (IVALID, IVKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused contract") };
    assert_eq!(r, Refusal::Later(SHAPE, CORNERS, IVALID, 7));
    // A contract that reads its own function.
    let own = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(CORNERS, Box::new(List::Nil))));
    let all = fns(vec![base_corners(List::Nil, List::Cons((CondKind::Ensures, own, 7, names(&[THIS])), Box::new(List::Nil)))]);
    let List::Cons(Model::Bare(_, _, _, r), _) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a refused contract") };
    assert_eq!(r, Refusal::Later(SHAPE, CORNERS, CORNERS, 7));
}

/// The check of an override reads a virtual function of the interface in the contract of the interface as the override of the
/// class. An interface whose contract reads a later function has no upcast, decision 0166.
#[test]
fn the_check_of_an_override_reads_the_functions_of_the_class() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let req = List::Cons((CondKind::Requires, Expr::Apply(IVALID, Box::new(List::Nil)), 7, names(&[THIS])), Box::new(List::Nil));
    let dvalid = Function { name: 314, line: 14, ret: Ty::Bool, body: one(Stmt::Return(Expr::Bool(true), 14)), ..derived_corners(List::Nil, List::Nil) };
    let all = fns(vec![base_valid(), base_corners(List::Nil, req), dvalid, derived_corners(List::Nil, List::Nil)]);
    let square = List::Cons((IVALID, (314, None)), Box::new(corners_member()));
    let sd = |shape: &[(u32, u32)]| {
        let List::Cons(s, _) = shape_of(shape) else { unreachable!() };
        List::Cons(s, Box::new(List::Cons((SQUARE, (12, List::Nil, square_copy(&square))), Box::new(List::Nil))))
    };
    let List::Cons(Ok(up), _) = translate_overrides(&bases, &all, &sd(&[(IVALID, IVKEY), (CORNERS, BKEY)])) else { panic!("an upcast") };
    let List::Cons(_, rest) = up.overrides else { panic!("the check of valid") };
    let List::Cons(o, _) = *rest else { panic!("the check of corners") };
    let on_square = DExpr::FCall(314, Box::new(List::Cons(DExpr::Var(THIS), Box::new(List::Nil))));
    assert_eq!(o.requires, List::Cons((on_square, 7), Box::new(List::Nil)));
    let late = translate_overrides(&bases, &all, &sd(&[(CORNERS, BKEY), (IVALID, IVKEY)]));
    assert_eq!(late, List::Cons(Err(Refusal::Later(SHAPE, CORNERS, IVALID, 7)), Box::new(List::Nil)));
}

fn square_copy(ms: &Members) -> Members {
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, p)), rest) => List::Cons((*n, (*k, p.as_ref().map(|(t, ps)| (*t, params_copy(ps))))), Box::new(square_copy(rest))),
    }
}

fn params_copy(ps: &Params) -> Params {
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => List::Cons((*n, *t), Box::new(params_copy(rest))),
    }
}

/// A contract of a function with a parameter `const Shape& s` reads `s.corners()` as the function of the interface, decision 0166.
#[test]
fn a_caller_reads_a_virtual_function_of_a_parameter() {
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Name(VX)), CORNERS, Box::new(List::Nil))));
    let count = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, ens, 19, names(&[VX])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(3, Ty::I32), 21)),
    };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), count]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of count") };
    let call = DExpr::AsInt(Box::new(DExpr::FCall(BKEY, Box::new(List::Cons(DExpr::Var(VX), Box::new(List::Nil))))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(call));
    assert_eq!(m.ensures, List::Cons((want, 19), Box::new(List::Nil)));
}

/// A value of a final class as an argument of a parameter of its interface is the upcast, decision 0166.
#[test]
fn an_upcast_is_a_value_of_the_interface() {
    let e = Expr::Cast(CastKind::Upcast(SQUARE, SHAPE), b(Expr::Var(VY, Ty::Struct(SQUARE))));
    assert_eq!(translate_code(&e, 30), Ok(DExpr::Upcast(SQUARE, SHAPE, Box::new(DExpr::Var(VY)))));
}

/// `this->x` in a contract reads `x`, and `this->f(a)` calls `f(a)`, decision 0166. `this` alone has no rule.
#[test]
fn this_and_an_arrow_read_the_object() {
    let k = 315;
    assert_eq!(parse_contract(&vec![Tok::This, Tok::Arrow, Tok::Ident(k)], 4), parse_contract(&vec![Tok::Ident(k)], 4));
    let call = vec![Tok::This, Tok::Arrow, Tok::Ident(IVALID), Tok::LParen, Tok::RParen, Tok::Op(BinOp::And), Tok::Ident(k)];
    assert_eq!(parse_contract(&call, 4), parse_contract(&call[2..].to_vec(), 4));
    assert_eq!(parse_contract(&vec![Tok::This], 4), Err(Refusal::Syntax(4)));
}

const MULB: u32 = 316;

/// A pure member function can have apply lines above its return. Its function calls each lemma before its value, in order,
/// decision 0167.
#[test]
fn a_pure_member_function_calls_its_lemmas_before_its_value() {
    let two = || Box::new(List::Cons(b(Expr::Int(2)), Box::new(List::Cons(b(Expr::Int(3)), Box::new(List::Nil)))));
    let body = List::Cons(
        Box::new(Stmt::Apply(MULB, two(), 14)),
        Box::new(List::Cons(Box::new(Stmt::Apply(LEM, two(), 15)), Box::new(one(Stmt::Return(Expr::Lit(4, Ty::I32), 16))))),
    );
    let f = Function { body, ..derived_corners(List::Nil, List::Nil) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &shapes(corners_member())) else { panic!("a full model") };
    let args = || Box::new(List::Cons(DExpr::Lit(2), Box::new(List::Cons(DExpr::Lit(3), Box::new(List::Nil)))));
    let want = DExpr::Lemma(MULB, args(), Box::new(DExpr::Lemma(LEM, args(), Box::new(lit32(4)))));
    assert_eq!(m.function, Some(want));
    // The method keeps the apply lines as statements before its return, decision 0099.
    assert!(matches!(&m.body, List::Cons(s, _) if matches!(&*s.0, DStmt::Apply(k, _) if *k == MULB)), "{:?}", m.body);
}

/// `p->f(a)` in a contract calls the member function `f` on the value of `p`, as `o.f(a)` calls it on `o`, decision 0168.
#[test]
fn an_arrow_call_reads_the_value_of_a_pointer() {
    let (p, f) = (317, 318);
    let none = parse_contract(&vec![Tok::Ident(p), Tok::Arrow, Tok::Ident(f), Tok::LParen, Tok::RParen], 4);
    assert_eq!(none, Ok(Expr::MApply(b(Expr::Value(b(Expr::Name(p)))), f, Box::new(List::Nil))));
    let one = parse_contract(&vec![Tok::Result, Tok::Arrow, Tok::Ident(f), Tok::LParen, Tok::Int(2), Tok::RParen], 4);
    assert_eq!(one, Ok(Expr::MApply(b(Expr::Value(b(Expr::Result))), f, Box::new(List::Cons(b(Expr::Int(2)), Box::new(List::Nil))))));
    // A field after the arrow stays a field.
    assert_eq!(parse_contract(&vec![Tok::Ident(p), Tok::Arrow, Tok::Ident(f)], 4), Ok(Expr::Field(b(Expr::Value(b(Expr::Name(p)))), f)));
}

/// A unique_ptr of an interface is an optional of it. A contract reads `p->corners()` as the function of the interface on the value
/// of `p`, and `std::make_unique` of a final class is the upcast of its value, decision 0168.
#[test]
fn a_unique_ptr_of_an_interface_is_an_optional_of_it() {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    assert_eq!(translate_ty(own, 3), Ok(DTy::Opt(Scalar::Struct(SHAPE))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::MApply(b(Expr::Value(b(Expr::Name(VX)))), CORNERS, Box::new(List::Nil))));
    let read = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, own), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, ens, 19, names(&[VX])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(3, Ty::I32), 21)),
    };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), read]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of read") };
    let get = DExpr::Get(Box::new(DExpr::Var(VX)));
    let call = DExpr::AsInt(Box::new(DExpr::FCall(BKEY, Box::new(List::Cons(get, Box::new(List::Nil))))));
    assert_eq!(m.ensures, List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(call)), 19), Box::new(List::Nil)));
    let made = Expr::Wrap(b(Expr::Cast(CastKind::Upcast(SQUARE, SHAPE), b(Expr::Construct(SQUARE, Box::new(List::Nil))))));
    let make = Function { name: 319, line: 30, params: List::Nil, ret: own, trusted: false, conds: List::Nil, body: one(Stmt::Return(made, 31)) };
    let Model::Full(m) = translate_function(&make, &List::Nil, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model of make") };
    let want = DExpr::Just(Box::new(DExpr::Upcast(SQUARE, SHAPE, Box::new(DExpr::Ctor(SQUARE, Box::new(List::Nil))))));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
}

const VBUMP: u32 = 320;
const BMKEY: u32 = 321;
const DMKEY: u32 = 322;

/// `virtual void bump() = 0;` of the interface Shape, a pure virtual function that writes its object, with `ensures true`.
fn base_bump() -> Function {
    let ens = List::Cons((CondKind::Ensures, Expr::Bool(true), 8, names(&[THIS])), Box::new(List::Nil));
    Function { name: BMKEY, line: 9, params: List::Cons((THIS, Ty::IfaceMut(SHAPE)), Box::new(List::Nil)), ret: Ty::Void, trusted: true, conds: ens, body: List::Nil }
}

/// `void bump() override {}` of the final class Square, with `ensures true`.
fn derived_bump() -> Function {
    let ens = List::Cons((CondKind::Ensures, Expr::Bool(true), 14, names(&[THIS])), Box::new(List::Nil));
    Function { name: DMKEY, line: 15, params: List::Cons((THIS, Ty::ThisMut(SQUARE)), Box::new(List::Nil)), ret: Ty::Void, trusted: false, conds: ens, body: List::Nil }
}

/// A pure virtual function that writes its object is a method that gives its object back, with no function in the model and no
/// line that links it to one. A reference of an interface is a value of it in and out, decision 0169.
#[test]
fn a_virtual_function_that_writes_is_a_method_with_no_function() {
    assert_eq!(translate_ty(Ty::IfaceMut(SHAPE), 3), Ok(DTy::Iface(SHAPE)));
    assert_eq!(translate_ty(Ty::Mut(Scalar::Struct(SHAPE)), 3), Ok(DTy::Struct(SHAPE)));
    let all = fns(vec![base_bump()]);
    let List::Cons(Model::Full(m), _) = translate_unit(&all, &shape_of(&[(VBUMP, BMKEY)])) else { panic!("a full model") };
    assert!(m.trusted && m.writes && m.function == None, "{m:?}");
    assert_eq!(m.ensures, List::Cons((DExpr::Bool(true), 8), Box::new(List::Nil)));
    // A function of a reference of the interface on its modifies line gives the reference back.
    let ping = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, Ty::Mut(Scalar::Struct(SHAPE))), Box::new(List::Nil)),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[VX], &[VX], List::Nil),
        body: List::Nil,
    };
    let Model::Full(m) = translate_function(&ping, &List::Nil, &shape_of(&[(VBUMP, BMKEY)])) else { panic!("a full model of ping") };
    assert_eq!(m.outs, List::Cons((VX, DTy::Struct(SHAPE)), Box::new(List::Nil)));
}

/// An override that writes is checked on the contracts: the check holds the ensures lines of the override as its promise. An
/// override with no method in the model is refused at its class, decision 0169.
#[test]
fn an_override_that_writes_is_checked_on_its_contract() {
    let bases = List::Cons((SQUARE, (names(&[SHAPE]), true)), Box::new(List::Nil));
    let square = List::Cons((VBUMP, (DMKEY, None)), Box::new(List::Nil));
    let sd = || {
        let List::Cons(s, _) = shape_of(&[(VBUMP, BMKEY)]) else { unreachable!() };
        List::Cons(s, Box::new(List::Cons((SQUARE, (12, List::Nil, square_copy(&square))), Box::new(List::Nil))))
    };
    let all = fns(vec![base_bump(), derived_bump()]);
    let List::Cons(Ok(up), _) = translate_overrides(&bases, &all, &sd()) else { panic!("an upcast") };
    let List::Cons(o, _) = up.overrides else { panic!("one check") };
    assert_eq!((o.base, o.derived), (BMKEY, DMKEY));
    assert_eq!(o.ensures, List::Cons((DExpr::Bool(true), 8), Box::new(List::Nil)));
    assert_eq!(o.promise, List::Cons((DExpr::Bool(true), 14), Box::new(List::Nil)));
    // A body with no rule leaves the override with no method in the model.
    let bad = Function { body: one(Stmt::Return(Expr::Unknown(7, 15), 15)), ..derived_bump() };
    let all = fns(vec![base_bump(), bad]);
    assert_eq!(translate_overrides(&bases, &all, &sd()), List::Cons(Err(Refusal::NoMethod(SQUARE, SHAPE, VBUMP, 12)), Box::new(List::Nil)));
}

/// A contract can call only a const virtual function of its interface, because a function that writes has no function in the
/// model, decision 0169.
#[test]
fn a_contract_cannot_call_a_virtual_function_that_writes() {
    let req = List::Cons((CondKind::Requires, Expr::Apply(VBUMP, Box::new(List::Nil)), 7, names(&[THIS])), Box::new(List::Nil));
    let all = fns(vec![base_bump(), base_corners(List::Nil, req)]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(VBUMP, BMKEY), (CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused contract") };
    assert_eq!(r, Refusal::NotPure(VBUMP, 7));
}

/// `c.value()` on an object of a struct calls its member `value`, as `c.f()` calls `f`. On an optional it still reads the value,
/// decision 0169.
#[test]
fn value_of_a_struct_calls_its_member_value() {
    let (counter, key) = (323, 324);
    let ps = List::Cons((THIS, Ty::This(counter)), Box::new(List::Nil));
    let table: Structs = List::Cons((counter, (3, List::Nil, List::Cons((VALUE_NAME, (key, Some((Ty::I32, ps)))), Box::new(List::Nil)))), Box::new(List::Nil));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Value(b(Expr::Name(VX)))));
    let f = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, Ty::Struct(counter)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, ens, 19, names(&[VX])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(3, Ty::I32), 21)),
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let call = DExpr::AsInt(Box::new(DExpr::FCall(key, Box::new(List::Cons(DExpr::Var(VX), Box::new(List::Nil))))));
    assert_eq!(m.ensures, List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(call)), 19), Box::new(List::Nil)));
}

/// A unique_ptr of an interface is an element of a sequence, and nowhere else outside 0142. Its element reads as a unique_ptr of
/// 0168, so a contract reads `v[0]->corners()`, decision 0170.
#[test]
fn a_unique_ptr_is_an_element_of_a_vector() {
    let own = Scalar::Own(SHAPE);
    assert_eq!(translate_ty(Ty::Seq(own, Extent::Dynamic), 3), Ok(DTy::Seq(own)));
    assert_eq!(translate_ty(Ty::MutSeq(own), 3), Ok(DTy::Seq(own)));
    assert_eq!(translate_ty(Ty::Vec(own), 3), Ok(DTy::Seq(own)));
    for t in [Ty::Opt(own), Ty::Mut(own), Ty::Ptr(own), Ty::Own(own)] {
        assert_eq!(translate_ty(t, 3), Err(Refusal::Element(3)), "{t:?}");
    }
    let call = Expr::MApply(b(Expr::Value(b(Expr::Index(b(Expr::Name(VX)), b(Expr::Int(0)))))), CORNERS, Box::new(List::Nil));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(call));
    let read = Function {
        name: BKEY2,
        line: 20,
        params: List::Cons((VX, Ty::Seq(own, Extent::Dynamic)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: false,
        conds: List::Cons((CondKind::Ensures, ens, 19, names(&[VX])), Box::new(List::Nil)),
        body: one(Stmt::Return(Expr::Lit(3, Ty::I32), 21)),
    };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), read]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of read") };
    let get = DExpr::Get(Box::new(DExpr::Index(Box::new(DExpr::Var(VX)), Box::new(DExpr::Lit(0)))));
    let want = DExpr::AsInt(Box::new(DExpr::FCall(BKEY, Box::new(List::Cons(get, Box::new(List::Nil))))));
    assert_eq!(m.ensures, List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(want)), 19), Box::new(List::Nil)));
}

/// A local vector with no initial value is the empty sequence, and push_back of std::make_unique of a final class adds the upcast
/// of the value that its constructor gives, decision 0170.
#[test]
fn a_local_vector_starts_empty_and_grows_by_make_unique() {
    let own = Scalar::Own(SHAPE);
    let made = Expr::Wrap(b(Expr::Cast(CastKind::Upcast(SQUARE, SHAPE), b(Expr::Construct(SQUARE, Box::new(List::Nil))))));
    let body = List::Cons(
        Box::new(Stmt::Local(LX, Ty::Vec(own), Expr::EmptyVec, 30)),
        Box::new(List::Cons(Box::new(Stmt::PushBack(LX, made, 31)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 32))))),
    );
    let f = Function { name: 325, line: 29, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model") };
    let List::Cons(first, rest) = strip(m.body) else { panic!("a body") };
    assert_eq!(*first.0, DStmt::Local(LX, DTy::Seq(own), DExpr::EmptySeq));
    let List::Cons(second, _) = *rest else { panic!("a push_back") };
    let some = DExpr::Just(Box::new(DExpr::Upcast(SQUARE, SHAPE, Box::new(DExpr::Ctor(SQUARE, Box::new(List::Nil))))));
    assert_eq!(*second.0, DStmt::Assign(LX, DExpr::Append(Box::new(DExpr::Var(LX)), Box::new(some))));
}

/// A call of a virtual function that writes, through an element of a vector by reference, writes the element back at its index. An
/// index that the call writes is refused, and a call that passes a local vector by reference writes it back, decision 0170.
#[test]
fn a_call_through_an_element_writes_the_element_back() {
    let own = Scalar::Own(SHAPE);
    let elem = |i: Expr| Expr::Value(b(Expr::Index(b(Expr::Var(VX, Ty::MutSeq(own))), b(i))));
    let call = |i: Expr| Stmt::Call(BMKEY, VBUMP, Box::new(List::Cons(b(elem(i)), Box::new(List::Nil))), 31);
    let caller = |body: Stmts| Function {
        name: 326,
        line: 30,
        params: List::Cons((VX, Ty::MutSeq(own)), Box::new(List::Nil)),
        ret: Ty::Void,
        trusted: false,
        conds: modifies(&[VX], &[VX], List::Nil),
        body,
    };
    let all = fns(vec![base_bump(), caller(one(call(Expr::Lit(0, Ty::U64))))]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(VBUMP, BMKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the caller") };
    let List::Cons(s, _) = strip(m.body) else { panic!("one statement") };
    let DStmt::UpdateAt(obj, idx, others, key, _) = *s.0 else { panic!("an update of an element: {:?}", s.0) };
    assert_eq!((obj, *idx, others, key), (Obj::Out(VX), DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0))), List::Nil, BMKEY));
    // An index that the call writes back is read twice, so it has no rule.
    let kparams = List::Cons((THIS, Ty::IfaceMut(SHAPE)), Box::new(List::Cons((VY, Ty::Mut(Scalar::U64)), Box::new(List::Nil))));
    let bumpk = Function { params: kparams, conds: modifies(&[VY], &[THIS, VY], List::Nil), ..base_bump() };
    let k = || Expr::Var(LX, Ty::U64);
    let hazard = Stmt::Call(BMKEY, VBUMP, Box::new(List::Cons(b(elem(k())), Box::new(List::Cons(b(k()), Box::new(List::Nil))))), 31);
    let body = List::Cons(Box::new(Stmt::Local(LX, Ty::U64, Expr::Lit(0, Ty::U64), 30)), Box::new(one(hazard)));
    let all = fns(vec![bumpk, caller(body)]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(VBUMP, BMKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused body") };
    assert_eq!(r, Refusal::IndexWritten(31));
    // A local vector passed to a vector by reference is written back to the local.
    let callee = Function { name: 327, line: 40, params: List::Cons((VY, Ty::MutSeq(Scalar::I32)), Box::new(List::Nil)), ret: Ty::Void, trusted: false, conds: modifies(&[VY], &[VY], List::Nil), body: List::Nil };
    let pass = Stmt::Call(327, 327, Box::new(List::Cons(b(Expr::Var(LX, Ty::Vec(Scalar::I32))), Box::new(List::Nil))), 46);
    let body = List::Cons(Box::new(Stmt::Local(LX, Ty::Vec(Scalar::I32), Expr::EmptyVec, 45)), Box::new(List::Cons(Box::new(pass), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 47))))));
    let local = Function { name: 328, line: 44, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    let all = fns(vec![callee, local]);
    let List::Cons(_, rest) = translate_unit(&all, &List::Nil) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the caller") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("a body") };
    let List::Cons(s, _) = *rest else { panic!("the call") };
    assert!(matches!(&*s.0, DStmt::Update(List::Cons(Obj::Local(v), _), 327, _) if *v == LX), "{:?}", s.0);
}

const MA: u32 = 331;
const MB: u32 = 332;
const MTAKE: u32 = 333;
const MP: u32 = 334;
const MCALLER: u32 = 335;

/// `std::make_unique<Square>()` as a `std::unique_ptr<Shape>`, decision 0168.
fn made_square() -> Expr {
    Expr::Wrap(b(Expr::Cast(CastKind::Upcast(SQUARE, SHAPE), b(Expr::Construct(SQUARE, Box::new(List::Nil))))))
}

/// `void take(std::unique_ptr<Shape> p);`, a trusted function with no contract that owns its parameter.
fn take_owned() -> Function {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    Function { name: MTAKE, line: 40, params: List::Cons((MP, own), Box::new(List::Nil)), ret: Ty::Void, trusted: true, conds: List::Nil, body: List::Nil }
}

/// A caller of `take` with the parameter `p` of type `std::unique_ptr<Shape>` by value, and the body given.
fn mover(body: Stmts) -> Function {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    Function { name: MCALLER, line: 44, params: List::Cons((MP, own), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body }
}

/// The model of the caller, the second of the unit with `take`.
fn moved_model(body: Stmts) -> Model {
    let all = fns(vec![take_owned(), mover(body)]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(m, _) = *rest else { panic!("the model of the caller") };
    m
}

/// `std::move(a)` reads the value of `a`. After a call that stands alone or the start value of a local, `a` is null in the model,
/// so a later read fails as a null read. A return moves a local or a parameter, and adds nothing after it, decision 0171.
#[test]
fn a_move_gives_the_value_and_leaves_the_local_null() {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    let body = List::Cons(
        Box::new(Stmt::Local(MA, own, made_square(), 45)),
        Box::new(List::Cons(
            Box::new(Stmt::Local(MB, own, Expr::Move(MA, own), 46)),
            Box::new(List::Cons(Box::new(Stmt::Call(MTAKE, MTAKE, Box::new(List::Cons(b(Expr::Move(MB, own)), Box::new(List::Nil))), 47)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 48))))),
        )),
    );
    let Model::Full(m) = moved_model(body) else { panic!("a full model") };
    // Each statement that moves a local is a Moved statement, which sets the local to null after it.
    let List::Cons(_, rest) = strip(m.body) else { panic!("the first local") };
    let List::Cons(s, rest) = *rest else { panic!("the second local") };
    assert_eq!(*s.0, DStmt::Moved(Box::new(DStmt::Local(MB, DTy::Opt(Scalar::Struct(SHAPE)), DExpr::Var(MA))), names(&[MA])));
    let List::Cons(s, _) = *rest else { panic!("the call") };
    assert!(matches!(&*s.0, DStmt::Moved(c, ns) if matches!(&**c, DStmt::CallStmt(k, _) if *k == MTAKE) && *ns == names(&[MB])), "{:?}", s.0);
    // A return of a moved local gives its value, and so does a return of a moved parameter.
    let body = List::Cons(Box::new(Stmt::Local(MA, own, made_square(), 45)), Box::new(one(Stmt::Return(Expr::Move(MA, own), 46))));
    let f = Function { ret: own, ..mover(body) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model of a return") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("the local") };
    assert_eq!(*rest, List::Cons((Box::new(DStmt::Return(DExpr::Var(MA))), 0), Box::new(List::Nil)));
    let f = Function { ret: own, ..mover(one(Stmt::Return(Expr::Move(MP, own), 45))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model of a parameter") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Var(MP))), 0), Box::new(List::Nil)));
}

/// The init list of a constructor is its return, so `f_(std::move(p))` gives the field the value of the parameter, decision 0171.
#[test]
fn a_constructor_moves_its_parameter_into_a_field() {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    let (holder, inner) = (336, 337);
    let table = List::Cons((holder, (3, List::Cons((inner, own), Box::new(List::Nil)), List::Nil)), Box::new(shape_of(&[(CORNERS, BKEY)])));
    let init = Expr::Construct(holder, Box::new(List::Cons(b(Expr::Move(MP, own)), Box::new(List::Nil))));
    let f = Function { name: 338, line: 9, params: List::Cons((MP, own), Box::new(List::Nil)), ret: Ty::This(holder), trusted: false, conds: List::Nil, body: one(Stmt::Return(init, 9)) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let want = DExpr::Ctor(holder, Box::new(List::Cons(DExpr::Var(MP), Box::new(List::Nil))));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
}

/// Two moves of one local in one statement, a move and a read of one local in one call, and a move in a condition have no rule,
/// decision 0171. A move of a parameter in a call has one since decision 0186.
#[test]
fn a_move_has_one_owner_and_a_place() {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    let arg = |v: u32| List::Cons(b(Expr::Move(v, own)), Box::new(List::Nil));
    let start = || Box::new(Stmt::Local(MA, own, made_square(), 45));
    let end = || Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 48)));
    // Two moves of a in one call.
    let two_ps = List::Cons((MP, own), Box::new(List::Cons((VY, own), Box::new(List::Nil))));
    let two = Function { params: two_ps, ..take_owned() };
    let twice = Stmt::Call(MTAKE, MTAKE, Box::new(List::Cons(b(Expr::Move(MA, own)), Box::new(arg(MA)))), 46);
    let all = fns(vec![two, mover(List::Cons(start(), Box::new(List::Cons(Box::new(twice), end()))))]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused body") };
    assert_eq!(r, Refusal::MoveRead(MA, 46));
    // A move of a and a read of a in one call.
    let two_ps = List::Cons((MP, own), Box::new(List::Cons((VY, own), Box::new(List::Nil))));
    let two = Function { params: two_ps, ..take_owned() };
    let beside = Stmt::Call(MTAKE, MTAKE, Box::new(List::Cons(b(Expr::Move(MA, own)), Box::new(List::Cons(b(Expr::Var(MA, own)), Box::new(List::Nil))))), 46);
    let all = fns(vec![two, mover(List::Cons(start(), Box::new(List::Cons(Box::new(beside), end()))))]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused body") };
    assert_eq!(r, Refusal::MoveRead(MA, 46));
    // A move of a parameter in a call is a move of the local of the parameter, decision 0186.
    let param = Stmt::Call(MTAKE, MTAKE, Box::new(arg(MP)), 46);
    assert!(matches!(moved_model(List::Cons(Box::new(param), end())), Model::Full(_)));
    // A move in the condition of an if has no place.
    let test = Function { ret: Ty::Bool, ..take_owned() };
    let cond = Stmt::If(Expr::Call(MTAKE, MTAKE, Box::new(arg(MA)), 46), Box::new(List::Nil), Box::new(List::Nil), 46);
    let all = fns(vec![test, mover(List::Cons(start(), Box::new(List::Cons(Box::new(cond), end()))))]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Bare(_, _, _, r), _) = *rest else { panic!("a refused body") };
    assert_eq!(r, Refusal::MovePlace(46));
}

const CELL: u32 = 470;
const TCV: u32 = 471;
const TCN: u32 = 472;

/// `struct Cell { int32_t value = 7; std::unique_ptr<Cell> next; }` as the table of the file.
fn cell_table() -> Structs {
    let fields = List::Cons((TCV, Ty::I32), Box::new(List::Cons((TCN, Ty::Own(Scalar::Struct(CELL))), Box::new(List::Nil))));
    List::Cons((CELL, (6, fields, List::Nil)), Box::new(List::Nil))
}

/// `std::make_unique<Cell>()`, decision 0186.
fn made_cell() -> Expr {
    Expr::Wrap(b(Expr::Construct(CELL, Box::new(List::Cons(b(Expr::Lit(7, Ty::I32)), Box::new(List::Cons(b(Expr::Nullopt), Box::new(List::Nil))))))))
}

/// `n->f = e` through a local unique_ptr writes the value that it owns. A move into the field leaves the source null after the
/// statement, decision 0186.
#[test]
fn a_field_write_through_a_local_unique_ptr_writes_the_value_it_owns() {
    let own = Ty::Own(Scalar::Struct(CELL));
    let body = List::Cons(
        Box::new(Stmt::Local(MA, own, made_cell(), 45)),
        Box::new(List::Cons(
            Box::new(Stmt::SetOwnField(MA, TCV, Expr::Lit(1, Ty::I32), 46)),
            Box::new(List::Cons(
                Box::new(Stmt::Local(MB, own, made_cell(), 47)),
                Box::new(List::Cons(Box::new(Stmt::SetOwnField(MA, TCN, Expr::Move(MB, own), 48)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 49))))),
            )),
        )),
    );
    let f = Function { name: 473, line: 44, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &cell_table()) else { panic!("a full model") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("the first local") };
    let List::Cons((write, _), rest) = *rest else { panic!("the write") };
    assert!(matches!(&*write, DStmt::SetOwnField(n, f, _) if *n == MA && *f == TCV), "{write:?}");
    let List::Cons(_, rest) = *rest else { panic!("the second local") };
    let List::Cons((moved, _), _) = *rest else { panic!("the move") };
    assert_eq!(*moved, DStmt::Moved(Box::new(DStmt::SetOwnField(MA, TCN, DExpr::Var(MB))), names(&[MB])));
}

/// A write through a parameter that the body does not move, a write that moves its own target, and a write to no field are
/// refused, decision 0186.
#[test]
fn a_field_write_through_a_unique_ptr_has_one_owner() {
    let own = Ty::Own(Scalar::Struct(CELL));
    let end = || Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 49)));
    let with = |params: Params, body: Stmts| Function { name: 474, line: 44, params, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    let p = List::Cons((MP, own), Box::new(List::Nil));
    let write = Stmt::SetOwnField(MP, TCV, Expr::Lit(1, Ty::I32), 46);
    assert_eq!(bare_refusal(translate_function(&with(p, List::Cons(Box::new(write), end())), &List::Nil, &cell_table())), Refusal::WriteParam(MP, 46));
    let start = || Box::new(Stmt::Local(MA, own, made_cell(), 45));
    let itself = Stmt::SetOwnField(MA, TCN, Expr::Move(MA, own), 46);
    let body = List::Cons(start(), Box::new(List::Cons(Box::new(itself), end())));
    assert_eq!(bare_refusal(translate_function(&with(List::Nil, body), &List::Nil, &cell_table())), Refusal::MoveRead(MA, 46));
    let nowhere = Stmt::SetOwnField(MA, 475, Expr::Lit(1, Ty::I32), 46);
    let body = List::Cons(start(), Box::new(List::Cons(Box::new(nowhere), end())));
    assert_eq!(bare_refusal(translate_function(&with(List::Nil, body), &List::Nil, &cell_table())), Refusal::NoField(475, 46));
}

/// A parameter by value that the body moves before its return is a local of the body. The body is a block that starts with the
/// local, so the contract still reads the parameter. A parameter that moves only in a return needs no local, decision 0186.
#[test]
fn a_parameter_that_moves_is_a_local_of_the_body() {
    let own = Ty::Own(Scalar::Struct(SHAPE));
    let arg = List::Cons(b(Expr::Move(MP, own)), Box::new(List::Nil));
    let body = List::Cons(Box::new(Stmt::Call(MTAKE, MTAKE, Box::new(arg), 46)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 48))));
    let Model::Full(m) = moved_model(body) else { panic!("a full model") };
    let List::Cons((block, _), rest) = strip(m.body) else { panic!("a body") };
    assert_eq!(*rest, List::Nil);
    let DStmt::Scope(inner) = *block else { panic!("a block: {block:?}") };
    let List::Cons((local, _), rest) = *inner else { panic!("the local of the parameter") };
    assert_eq!(*local, DStmt::Local(MP, DTy::Opt(Scalar::Struct(SHAPE)), DExpr::Var(MP)));
    let List::Cons((call, _), _) = *rest else { panic!("the call") };
    assert!(matches!(&*call, DStmt::Moved(c, ns) if matches!(&**c, DStmt::CallStmt(k, _) if *k == MTAKE) && *ns == names(&[MP])), "{call:?}");
    // A move in a branch is a move of the body too.
    let arg = List::Cons(b(Expr::Move(MP, own)), Box::new(List::Nil));
    let branch = Stmt::If(Expr::Bool(true), Box::new(one(Stmt::Call(MTAKE, MTAKE, Box::new(arg), 46))), Box::new(List::Nil), 46);
    let Model::Full(m) = moved_model(List::Cons(Box::new(branch), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 48))))) else { panic!("a full model of a branch") };
    let List::Cons((block, _), _) = strip(m.body) else { panic!("a body") };
    assert!(matches!(&*block, DStmt::Scope(_)), "{block:?}");
    // A parameter that moves only in a return needs no local.
    let f = Function { ret: own, ..mover(one(Stmt::Return(Expr::Move(MP, own), 45))) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &shape_of(&[(CORNERS, BKEY)])) else { panic!("a full model of a return") };
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::Var(MP))), 0), Box::new(List::Nil)));
}

/// A unique_ptr of a struct or an interface is a field, as an optional of it. A unique_ptr of a scalar is no field yet, decision 0171.
#[test]
fn a_unique_ptr_of_a_struct_is_a_field() {
    let holder = |t: Ty| List::Cons((336, (4, List::Cons((337, t), Box::new(List::Nil)), List::Nil)), Box::new(List::Nil));
    let want = List::Cons((337, DTy::Opt(Scalar::Struct(SHAPE))), Box::new(List::Nil));
    assert_eq!(translate_structs(&holder(Ty::Own(Scalar::Struct(SHAPE)))), List::Cons(Ok((336, want)), Box::new(List::Nil)));
    assert_eq!(translate_structs(&holder(Ty::Own(Scalar::I32))), List::Cons(Err(Refusal::Element(4)), Box::new(List::Nil)));
}

/// `s.corners()` on a parameter `const Shape& s`, decision 0166.
fn corners_of(v: u32) -> Expr {
    Expr::Call(BKEY, CORNERS, Box::new(List::Cons(b(Expr::Var(v, Ty::IfaceRef(SHAPE))), Box::new(List::Nil))), 21)
}

/// The function of `corners` on the value `v`.
fn corners_fn(v: u32) -> DExpr {
    DExpr::FCall(BKEY, Box::new(List::Cons(DExpr::Var(v), Box::new(List::Nil))))
}

/// A call of a const virtual function of an interface is its function in code, also on the right of && where no call runs before
/// the statement, decision 0172.
#[test]
fn a_virtual_call_in_code_is_its_function() {
    let ps = List::Cons((VY, Ty::I32), Box::new(List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil))));
    let test = Expr::Bin(BinOp::Gt, b(corners_of(VX)), b(Expr::Lit(3, Ty::I32)));
    let e = Expr::Bin(BinOp::And, b(Expr::Bin(BinOp::Gt, b(Expr::Var(VY, Ty::I32)), b(Expr::Lit(0, Ty::I32)))), b(test));
    let f = Function { name: 340, line: 20, params: ps, ret: Ty::Bool, trusted: false, conds: List::Nil, body: one(Stmt::Return(e, 21)) };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), f]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the caller") };
    let left = DExpr::Bin(BinOp::Gt, Box::new(DExpr::Var(VY)), Box::new(lit32(0)));
    let right = DExpr::Bin(BinOp::Gt, Box::new(corners_fn(VX)), Box::new(lit32(3)));
    let want = DExpr::Bin(BinOp::And, Box::new(left), Box::new(right));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
}

/// A pure member function can hold a local before its return, and can call a const virtual function of an interface as the start
/// value of the local or as the value of the return. Its function in the model holds the local and the call, decision 0172.
#[test]
fn a_pure_member_function_holds_locals_and_virtual_calls() {
    let ps = List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil));
    let all = fns(vec![base_corners(List::Nil, at_least_three())]);
    let local = List::Cons(Box::new(Stmt::Local(LX, Ty::I32, corners_of(VX), 20)), Box::new(one(Stmt::Return(Expr::Var(LX, Ty::I32), 21))));
    let f = Function { body: local, ..derived_corners(ps, List::Nil) };
    let Model::Full(m) = translate_function(&f, &all, &shapes(corners_member())) else { panic!("a full model") };
    assert_eq!(m.function, Some(DExpr::Let(LX, DTy::Int32, Box::new(corners_fn(VX)), Box::new(DExpr::Var(LX)))));
    let ps = List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil));
    let f = Function { body: one(Stmt::Return(corners_of(VX), 21)), ..derived_corners(ps, List::Nil) };
    let Model::Full(m) = translate_function(&f, &all, &shapes(corners_member())) else { panic!("a full model") };
    assert_eq!(m.function, Some(corners_fn(VX)));
}

/// A body that writes a local, or that calls a member function of its own class, is no pure body, decision 0172.
#[test]
fn a_written_local_or_an_own_call_is_no_pure_body() {
    let all = fns(vec![base_corners(List::Nil, at_least_three())]);
    let written = List::Cons(
        Box::new(Stmt::Local(LX, Ty::I32, Expr::Lit(4, Ty::I32), 20)),
        Box::new(List::Cons(Box::new(Stmt::Assign(LX, Expr::Lit(5, Ty::I32), 21)), Box::new(one(Stmt::Return(Expr::Var(LX, Ty::I32), 22))))),
    );
    let f = Function { body: written, ..derived_corners(List::Nil, List::Nil) };
    let Model::Full(m) = translate_function(&f, &all, &shapes(corners_member())) else { panic!("a full model") };
    assert_eq!(m.function, None);
    // A call of the class's own member corners, through its object.
    let own = Expr::Call(DKEY, CORNERS, Box::new(List::Cons(b(Expr::Var(THIS, Ty::This(SQUARE))), Box::new(List::Nil))), 21);
    let f = Function { name: 341, body: one(Stmt::Return(own, 21)), ..derived_corners(List::Nil, List::Nil) };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), derived_corners(List::Nil, List::Nil)]);
    let Model::Full(m) = translate_function(&f, &all, &shapes(corners_member())) else { panic!("a full model of the caller") };
    assert_eq!(m.function, None);
}

/// A call of a const virtual function in a loop condition is its function, decision 0172.
#[test]
fn a_virtual_call_in_a_loop_condition_is_its_function() {
    let ps = List::Cons((VX, Ty::IfaceRef(SHAPE)), Box::new(List::Nil));
    let test = Expr::Bin(BinOp::Ge, b(corners_of(VX)), b(Expr::Lit(0, Ty::I32)));
    let lp = Stmt::While(test, Box::new(List::Nil), Box::new(List::Nil), 21);
    let f = Function { name: 342, line: 20, params: ps, ret: Ty::Void, trusted: false, conds: List::Nil, body: one(lp) };
    let all = fns(vec![base_corners(List::Nil, at_least_three()), f]);
    let List::Cons(_, rest) = translate_unit(&all, &shape_of(&[(CORNERS, BKEY)])) else { panic!("two models") };
    let List::Cons(Model::Full(m), _) = *rest else { panic!("a full model of the loop") };
    let want = DExpr::Bin(BinOp::Ge, Box::new(corners_fn(VX)), Box::new(lit32(0)));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::While(want, List::Nil, List::Nil, Box::new(List::Nil))), 0), Box::new(List::Nil)));
}

const GT: u32 = 350;
const GB2: u32 = 351;
const GS: u32 = 352;
const GADD: u32 = 353;
const GADDNM: u32 = 354;
const GF: u32 = 355;

/// The globals of a file in the order of their definitions: `int32_t total`, `int32_t b`, `double scale`.
fn file_globals() -> Params {
    List::Cons((GT, Ty::I32), Box::new(List::Cons((GB2, Ty::I32), Box::new(List::Cons((GS, Ty::F64), Box::new(List::Nil))))))
}

/// A contract line that lists the global `g`, on a declaration with the parameters `ps`.
fn lists(k: CondKind, g: u32, line: u32, ps: &[u32]) -> (CondKind, Expr, u32, Names) {
    (k, Expr::Name(g), line, names(ps))
}

/// `void add(int32_t x) { total += x; }` with `//@ modifies total`.
fn global_add() -> Function {
    let body = one(Stmt::Assign(GT, Expr::Bin(BinOp::Add, b(Expr::Var(GT, Ty::I32)), b(Expr::Var(X, Ty::I32))), 12));
    let conds = List::Cons(lists(CondKind::Modifies, GT, 9, &[X]), Box::new(List::Nil));
    Function { name: GADD, line: 11, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::Void, trusted: false, conds, body }
}

/// A function of the key GF with no parameter, the lines and the body given.
fn global_user(conds: Conds, body: Stmts) -> Function {
    Function { name: GF, line: 20, params: List::Nil, ret: Ty::I32, trusted: false, conds, body }
}

fn fn_list(fs: &Fns) -> Vec<&Function> {
    let mut v = Vec::new();
    let mut rest = fs;
    while let List::Cons(f, next) = rest {
        v.push(&**f);
        rest = next;
    }
    v
}

/// The refusal of a model, bare or refused.
fn refusal_of(m: &Model) -> Refusal {
    match m {
        Model::Bare(_, _, _, r) => *r,
        Model::Refused(r) => *r,
        other => panic!("no refusal: {other:?}"),
    }
}

/// A global on a modifies line is a reference parameter, and one on a reads line only is a parameter by value. Each comes after
/// the parameters of C++, in the order of the globals in the file. The pass types each global in the body by them, adds the
/// globals to the names of each contract line, and consumes the reads lines. A function that lists no global keeps its
/// parameters, decision 0173.
#[test]
fn a_listed_global_is_an_implicit_parameter() {
    let reads = global_user(List::Cons(lists(CondKind::Reads, GT, 16, &[]), Box::new(List::Nil)), one(Stmt::Return(Expr::Var(GT, Ty::I32), 18)));
    let both = global_user(
        List::Cons(lists(CondKind::Modifies, GB2, 24, &[]), Box::new(List::Cons(lists(CondKind::Modifies, GT, 25, &[]), Box::new(List::Nil)))),
        one(Stmt::Return(Expr::Lit(0, Ty::I32), 27)),
    );
    let plain = Function { name: GF + 10, ..global_user(List::Nil, one(Stmt::Return(Expr::Lit(0, Ty::I32), 30))) };
    let out = globalize(&fns(vec![global_add(), reads, Function { name: GF + 20, ..both }, plain]), &file_globals());
    let fs = fn_list(&out);
    let mt = (GT, Ty::Mut(Scalar::I32));
    assert_eq!(fs[0].params, List::Cons((X, Ty::I32), Box::new(List::Cons(mt, Box::new(List::Nil)))));
    let want = Stmt::Assign(GT, Expr::Bin(BinOp::Add, b(Expr::Var(GT, Ty::Mut(Scalar::I32))), b(Expr::Var(X, Ty::I32))), 12);
    assert_eq!(fs[0].body, one(want));
    assert_eq!(fs[0].conds, List::Cons(lists(CondKind::Modifies, GT, 9, &[X, GT]), Box::new(List::Nil)));
    assert_eq!(fs[1].params, List::Cons((GT, Ty::I32), Box::new(List::Nil)));
    assert_eq!(fs[1].conds, List::Nil);
    assert_eq!(fs[1].body, one(Stmt::Return(Expr::Var(GT, Ty::I32), 18)));
    assert_eq!(fs[2].params, List::Cons(mt, Box::new(List::Cons((GB2, Ty::Mut(Scalar::I32)), Box::new(List::Nil)))));
    assert_eq!(fs[3].params, List::Nil);
    assert_eq!(fs[3].conds, List::Nil);
}

/// A call gives the callee each global it lists, as the parameter of the caller of that name, decision 0173.
#[test]
fn a_call_passes_the_globals_of_its_callee() {
    let call = Stmt::Call(GADD, GADDNM, Box::new(List::Cons(b(Expr::Var(X, Ty::I32)), Box::new(List::Nil))), 31);
    let caller = Function {
        params: List::Cons((X, Ty::I32), Box::new(List::Nil)),
        ret: Ty::Void,
        ..global_user(List::Cons(lists(CondKind::Modifies, GT, 28, &[X]), Box::new(List::Nil)), one(call))
    };
    let out = globalize(&fns(vec![global_add(), caller]), &file_globals());
    let fs = fn_list(&out);
    let args = List::Cons(b(Expr::Var(X, Ty::I32)), Box::new(List::Cons(b(Expr::Var(GT, Ty::Mut(Scalar::I32))), Box::new(List::Nil))));
    assert_eq!(fs[1].body, one(Stmt::Call(GADD, GADDNM, Box::new(args), 31)));
}

/// A function with a reads line that calls a function with the global on its modifies line, a global with the name of a
/// parameter, a member function that lists a global, a global of a type with no rule, and a global that no line lists are each
/// refused, decision 0173.
#[test]
fn a_global_with_no_rule_is_refused_by_the_pass() {
    let unit = |fs: Vec<Function>| translate_unit(&globalize(&fns(fs), &file_globals()), &List::Nil);
    let last = |ms: Models| {
        let mut rest = ms;
        loop {
            match rest {
                List::Cons(m, next) => if *next == List::Nil { return m } else { rest = *next },
                List::Nil => panic!("no model"),
            }
        }
    };
    let call = Stmt::Call(GADD, GADDNM, Box::new(List::Cons(b(Expr::Lit(1, Ty::I32)), Box::new(List::Nil))), 31);
    let reader = Function { ret: Ty::Void, ..global_user(List::Cons(lists(CondKind::Reads, GT, 28, &[]), Box::new(List::Nil)), one(call)) };
    assert_eq!(refusal_of(&last(unit(vec![global_add(), reader]))), Refusal::ReadsOnly(GADDNM, GT, 31));
    let clash = Function { params: List::Cons((GT, Ty::I32), Box::new(List::Nil)), ..global_user(List::Cons(lists(CondKind::Modifies, GT, 19, &[GT]), Box::new(List::Nil)), one(Stmt::Return(Expr::Lit(0, Ty::I32), 21))) };
    assert_eq!(refusal_of(&last(unit(vec![clash]))), Refusal::GlobalClash(GT, 19));
    // A member that writes its object can list a global, decision 0178. A const member cannot yet, since its twin takes no global.
    let member = Function { params: List::Cons((THIS, Ty::ThisMut(COUNTER)), Box::new(List::Nil)), ret: Ty::Void, ..global_user(List::Cons(lists(CondKind::Modifies, GT, 9, &[]), Box::new(List::Nil)), List::Nil) };
    let out = globalize(&fns(vec![member]), &file_globals());
    assert!(!any_bad(&fn_list(&out)[0].conds));
    assert_eq!(fn_list(&out)[0].params, List::Cons((THIS, Ty::ThisMut(COUNTER)), Box::new(List::Cons((GT, Ty::Mut(Scalar::I32)), Box::new(List::Nil)))));
    let reader = Function { params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)), ..global_user(List::Cons(lists(CondKind::Reads, GT, 9, &[]), Box::new(List::Nil)), List::Nil) };
    assert_eq!(refusal_of(&last(unit(vec![reader]))), Refusal::MemberGlobal(9));
    let virt = Function { params: List::Cons((THIS, Ty::IfaceMut(COUNTER)), Box::new(List::Nil)), ret: Ty::Void, ..global_user(List::Cons(lists(CondKind::Modifies, GT, 9, &[]), Box::new(List::Nil)), List::Nil) };
    assert_eq!(refusal_of(&last(unit(vec![virt]))), Refusal::MemberGlobal(9));
    let real = global_user(List::Cons(lists(CondKind::Reads, GS, 13, &[]), Box::new(List::Nil)), one(Stmt::Return(Expr::Lit(0, Ty::I32), 16)));
    assert_eq!(refusal_of(&last(unit(vec![real]))), Refusal::GlobalType(13));
    let unlisted = global_user(List::Nil, one(Stmt::Return(Expr::Var(GT, Ty::I32), 22)));
    assert_eq!(refusal_of(&last(unit(vec![unlisted]))), Refusal::Name(GT, 22));
    // A parameter of the name of a global that the function does not list hides the global, as in C++.
    let hidden = Function { params: List::Cons((GT, Ty::I32), Box::new(List::Nil)), ..global_user(List::Nil, one(Stmt::Return(Expr::Var(GT, Ty::I32), 22))) };
    let out = globalize(&fns(vec![hidden]), &file_globals());
    assert_eq!(fn_list(&out)[0].body, one(Stmt::Return(Expr::Var(GT, Ty::I32), 22)));
    assert!(matches!(last(unit(vec![Function { params: List::Cons((GT, Ty::I32), Box::new(List::Nil)), ..global_user(List::Nil, one(Stmt::Return(Expr::Var(GT, Ty::I32), 22))) }])), Model::Full(_)));
}

/// A parameter of a lambda hides a global of its name inside the lambda, and a comparator reads a listed global as the function
/// does, decision 0173.
#[test]
fn a_lambda_parameter_hides_a_global_and_a_comparator_reads_it() {
    let modifies = || List::Cons(lists(CondKind::Modifies, GT, 7, &[VX]), Box::new(List::Nil));
    let test = || Expr::Bin(BinOp::Gt, b(Expr::Var(GT, Ty::I32)), b(Expr::Lit(0, Ty::I32)));
    let count = Expr::CountIf(b(Expr::Var(VX, Ty::Seq(Scalar::I32, Extent::Dynamic))), GT, Ty::I32, b(test()));
    let counter = Function { params: List::Cons((VX, Ty::Seq(Scalar::I32, Extent::Dynamic)), Box::new(List::Nil)), ..global_user(modifies(), one(Stmt::Return(count, 18))) };
    let sorter = Function {
        name: GF + 30,
        params: List::Cons((VX, Ty::MutSeq(Scalar::I32)), Box::new(List::Nil)),
        ret: Ty::Void,
        ..global_user(modifies(), one(Stmt::SortBy(VX, A, B, Ty::I32, test(), 20)))
    };
    let out = globalize(&fns(vec![counter, sorter]), &file_globals());
    let fs = fn_list(&out);
    let kept = Expr::CountIf(b(Expr::Var(VX, Ty::Seq(Scalar::I32, Extent::Dynamic))), GT, Ty::I32, b(test()));
    assert_eq!(fs[0].body, one(Stmt::Return(kept, 18)));
    let read = Expr::Bin(BinOp::Gt, b(Expr::Var(GT, Ty::Mut(Scalar::I32))), b(Expr::Lit(0, Ty::I32)));
    assert_eq!(fs[1].body, one(Stmt::SortBy(VX, A, B, Ty::I32, read, 20)));
}

const TALLY: u32 = 360;
const TCOUNT: u32 = 361;
const TVALID: u32 = 362;
const TCOUNTF: u32 = 363;
const TBUMP: u32 = 364;
const KTV: u32 = 365;
const KTC: u32 = 366;
const KTB: u32 = 367;
const CMADE: u32 = 368;
const CMADEF: u32 = 369;
const KMADE: u32 = 370;

/// The class Tally with no field and the statics `Tally::valid` and `Tally::count`, whose twins read the static data member
/// `Tally::count_`, and `Tally::bump`, which writes it, decision 0174.
fn tally_table() -> Structs {
    let g = || List::Cons((TCOUNT, Ty::I32), Box::new(List::Nil));
    let ms = List::Cons(
        (TVALID, (KTV, Some((Ty::Bool, g())))),
        Box::new(List::Cons((TCOUNTF, (KTC, Some((Ty::I32, g())))), Box::new(List::Cons((TBUMP, (KTB, None)), Box::new(List::Nil))))),
    );
    List::Cons((TALLY, (5, List::Nil, ms)), Box::new(List::Nil))
}

/// The twin of `Tally::f` on the value `d` of the static data member.
fn twin(key: u32, d: DExpr) -> DExpr {
    DExpr::FCall(key, Box::new(List::Cons(d, Box::new(List::Nil))))
}

/// A contract calls the twin of a static member function with the values of its globals: before in a requires line and under
/// `old`, after in an ensures line, decision 0174.
#[test]
fn a_contract_calls_the_twin_of_a_static() {
    let call = |k: u32| Expr::Apply(k, Box::new(List::Nil));
    let conds = List::Cons(
        (CondKind::Requires, call(TVALID), 20, names(&[TCOUNT])),
        Box::new(List::Cons(
            (CondKind::Modifies, Expr::Name(TCOUNT), 21, names(&[TCOUNT])),
            Box::new(List::Cons(
                (CondKind::Ensures, call(TVALID), 22, names(&[TCOUNT])),
                Box::new(List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(call(TCOUNTF)), b(Expr::Old(b(call(TCOUNTF))))), 22, names(&[TCOUNT])), Box::new(List::Nil))),
            )),
        )),
    );
    let bump = Function { name: KTB, line: 23, params: List::Cons((TCOUNT, Ty::Mut(Scalar::I32)), Box::new(List::Nil)), ret: Ty::Void, trusted: true, conds, body: List::Nil };
    let Model::Full(m) = translate_function(&bump, &List::Nil, &tally_table()) else { panic!("a full model") };
    assert_eq!(strip_conds(m.requires), List::Cons((twin(KTV, DExpr::Var(TCOUNT)), 0), Box::new(List::Nil)));
    let after = twin(KTV, DExpr::Out(TCOUNT));
    let count = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(twin(KTC, DExpr::Out(TCOUNT))))), Box::new(DExpr::AsInt(Box::new(twin(KTC, DExpr::Var(TCOUNT))))));
    assert_eq!(strip_conds(m.ensures), List::Cons((after, 0), Box::new(List::Cons((count, 0), Box::new(List::Nil)))));
}

/// A static that writes has no twin, so a contract that calls it is refused, decision 0174.
#[test]
fn a_static_that_writes_is_no_pure_function() {
    let modifies = List::Cons((CondKind::Modifies, Expr::Name(TCOUNT), 18, names(&[TCOUNT])), Box::new(List::Nil));
    let conds = List::Cons((CondKind::Ensures, Expr::Apply(TBUMP, Box::new(List::Nil)), 19, names(&[TCOUNT])), Box::new(modifies));
    let f = Function { name: 371, line: 20, params: List::Cons((TCOUNT, Ty::Mut(Scalar::I32)), Box::new(List::Nil)), ret: Ty::Bool, trusted: true, conds, body: List::Nil };
    let m = translate_function(&f, &List::Nil, &tally_table());
    assert_eq!(refusal_of(&m), Refusal::NotPure(TBUMP, 19));
}

/// A twin reads its globals by name, so a contract of a function that lists no such global is refused at its line. A twin cannot
/// bring an unlisted global into a contract, decision 0174.
#[test]
fn a_twin_reads_a_global_the_caller_does_not_list() {
    let conds = List::Cons((CondKind::Requires, Expr::Apply(TVALID, Box::new(List::Nil)), 30, names(&[])), Box::new(List::Nil));
    let f = Function { name: 372, line: 31, params: List::Nil, ret: Ty::Void, trusted: true, conds, body: List::Nil };
    let m = translate_function(&f, &List::Nil, &tally_table());
    assert_eq!(refusal_of(&m), Refusal::Name(TCOUNT, 30));
}

/// A struct keeps its const members beside its statics: `c.value()` passes the object, and `Counter::made_count()` the static
/// data member, decision 0174.
#[test]
fn a_struct_keeps_its_const_members_beside_a_static() {
    let this_ps = List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil));
    let ms = List::Cons(
        (VALUE_NAME, (NKEY, Some((Ty::I32, this_ps)))),
        Box::new(List::Cons((CMADEF, (KMADE, Some((Ty::I32, List::Cons((CMADE, Ty::I32), Box::new(List::Nil)))))), Box::new(List::Nil))),
    );
    let table: Structs = List::Cons((COUNTER, (4, List::Cons((CN, Ty::I32), Box::new(List::Nil)), ms)), Box::new(List::Nil));
    let sum = Expr::Bin(BinOp::Add, b(Expr::MApply(b(Expr::Name(VX)), VALUE_NAME, Box::new(List::Nil))), b(Expr::Apply(CMADEF, Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(sum));
    let ps = List::Cons((VX, Ty::Struct(COUNTER)), Box::new(List::Cons((CMADE, Ty::I32), Box::new(List::Nil))));
    let f = Function { name: 373, line: 40, params: ps, ret: Ty::I32, trusted: true, conds: List::Cons((CondKind::Ensures, ens, 39, names(&[VX, CMADE])), Box::new(List::Nil)), body: List::Nil };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let value = DExpr::AsInt(Box::new(twin(NKEY, DExpr::Var(VX))));
    let made = DExpr::AsInt(Box::new(twin(KMADE, DExpr::Var(CMADE))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::Bin(BinOp::Add, Box::new(value), Box::new(made))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
}

/// A static member function has no object, so it can list a global, decision 0174.
#[test]
fn a_static_lists_a_global() {
    let f = Function { name: GF + 40, ..global_user(List::Cons(lists(CondKind::Modifies, GT, 9, &[]), Box::new(List::Nil)), one(Stmt::Return(Expr::Lit(0, Ty::I32), 10))) };
    let out = globalize(&fns(vec![f]), &file_globals());
    assert!(!any_bad(&fn_list(&out)[0].conds));
}

const TABOVE: u32 = 374;
const KTA: u32 = 375;

/// A twin with an argument takes its arguments, converted to their types, before the values of its globals, decision 0174.
#[test]
fn a_twin_takes_its_arguments_before_its_globals() {
    let twin_ps = List::Cons((X, Ty::I32), Box::new(List::Cons((TCOUNT, Ty::I32), Box::new(List::Nil))));
    let table: Structs = List::Cons((TALLY, (5, List::Nil, List::Cons((TABOVE, (KTA, Some((Ty::Bool, twin_ps)))), Box::new(List::Nil)))), Box::new(List::Nil));
    let req = Expr::Apply(TABOVE, Box::new(List::Cons(b(Expr::Int(3)), Box::new(List::Nil))));
    let conds = List::Cons((CondKind::Requires, req, 30, names(&[TCOUNT])), Box::new(List::Nil));
    let f = Function { name: 376, line: 31, params: List::Cons((TCOUNT, Ty::I32), Box::new(List::Nil)), ret: Ty::Void, trusted: true, conds, body: List::Nil };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let args = List::Cons(DExpr::Conv(DTy::Int32, Box::new(DExpr::Lit(3))), Box::new(List::Cons(DExpr::Var(TCOUNT), Box::new(List::Nil))));
    assert_eq!(strip_conds(m.requires), List::Cons((DExpr::FCall(KTA, Box::new(args)), 0), Box::new(List::Nil)));
}

/// A twin with an object of any kind is no static, so a contract call of its name with no object stays a call of the companion
/// file, decision 0174.
#[test]
fn a_virtual_function_is_no_static() {
    let iface_ps = List::Cons((THIS, Ty::Iface(SHAPE)), Box::new(List::Nil));
    let shape = (SHAPE, (5, List::Nil, List::Cons((CORNERS, (BKEY, Some((Ty::I32, iface_ps)))), Box::new(List::Nil))));
    let table: Structs = List::Cons((COUNTER, (3, List::Nil, List::Nil)), Box::new(List::Cons(shape, Box::new(List::Nil))));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(CORNERS, Box::new(List::Nil))));
    let f = Function {
        name: 377,
        line: 41,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::I32,
        trusted: true,
        conds: List::Cons((CondKind::Ensures, ens, 40, names(&[THIS])), Box::new(List::Nil)),
        body: List::Nil,
    };
    let Model::Full(m) = translate_function(&f, &List::Nil, &table) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::Apply(CORNERS, Box::new(List::Nil))));
    assert!(matches!(&m.ensures, List::Cons((d, _), _) if *d == want), "{:?}", m.ensures);
}

const BA: u32 = 380;
const BB: u32 = 381;

/// `a & b` in code on two unsigned values is BitAnd of the prelude on their integers, back in the type under its range check. A
/// bit operator on a signed value has no rule, decision 0175.
#[test]
fn a_bit_operator_is_a_function_of_the_prelude() {
    let ps = |t: Ty| List::Cons((BA, t), Box::new(List::Cons((BB, t), Box::new(List::Nil))));
    let bits = |op: BinOp, t: Ty| Expr::Bits(op, b(Expr::Var(BA, t)), b(Expr::Var(BB, t)), t);
    let f = Function { name: 382, line: 20, params: ps(Ty::U32), ret: Ty::U32, trusted: false, conds: List::Nil, body: one(Stmt::Return(bits(BinOp::BitAnd, Ty::U32), 21)) };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Conv(DTy::UInt32, Box::new(DExpr::BitOp(BinOp::BitAnd, Box::new(DExpr::AsInt(Box::new(DExpr::Var(BA)))), Box::new(DExpr::AsInt(Box::new(DExpr::Var(BB)))))));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(want)), 0), Box::new(List::Nil)));
    let g = Function { params: ps(Ty::I32), ret: Ty::I32, body: one(Stmt::Return(bits(BinOp::BitOr, Ty::I32), 21)), ..f };
    assert_eq!(refusal_of(&translate_function(&g, &List::Nil, &List::Nil)), Refusal::SignedBits(21));
}

/// A contract reads `a & b` as BitAnd, and `static_cast<T>(e)` as the value of `e` when each value of its type fits `T`. A cast
/// that can change the value is refused at its line, decision 0175.
#[test]
fn a_contract_reads_bits_and_a_cast_that_keeps_the_value() {
    let ens = |e: Expr| List::Cons((CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(e)), 19, names(&[BA, BB])), Box::new(List::Nil));
    let f = |e: Expr| Function { name: 383, line: 20, params: List::Cons((BA, Ty::U32), Box::new(List::Cons((BB, Ty::U32), Box::new(List::Nil)))), ret: Ty::U32, trusted: true, conds: ens(e), body: List::Nil };
    let Model::Full(m) = translate_function(&f(Expr::StaticCast(Ty::U32, b(Expr::Name(BA)))), &List::Nil, &List::Nil) else { panic!("a full model") };
    let res = || Box::new(DExpr::AsInt(Box::new(DExpr::Result)));
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::Bin(BinOp::Eq, res(), Box::new(DExpr::AsInt(Box::new(DExpr::Var(BA))))), 0), Box::new(List::Nil)));
    let Model::Full(m) = translate_function(&f(Expr::Bin(BinOp::BitAnd, b(Expr::Name(BA)), b(Expr::Name(BB)))), &List::Nil, &List::Nil) else { panic!("a full model") };
    let and = DExpr::BitOp(BinOp::BitAnd, Box::new(DExpr::AsInt(Box::new(DExpr::Var(BA)))), Box::new(DExpr::AsInt(Box::new(DExpr::Var(BB)))));
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::Bin(BinOp::Eq, res(), Box::new(and)), 0), Box::new(List::Nil)));
    let m = translate_function(&f(Expr::StaticCast(Ty::U8, b(Expr::Name(BA)))), &List::Nil, &List::Nil);
    assert_eq!(refusal_of(&m), Refusal::ContractCast(19));
    // Each uint32 fits an int64, and not each fits an int32.
    let m = translate_function(&f(Expr::StaticCast(Ty::I32, b(Expr::Name(BA)))), &List::Nil, &List::Nil);
    assert_eq!(refusal_of(&m), Refusal::ContractCast(19));
    let Model::Full(m) = translate_function(&f(Expr::StaticCast(Ty::I64, b(Expr::Name(BA)))), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::Bin(BinOp::Eq, res(), Box::new(DExpr::AsInt(Box::new(DExpr::Var(BA))))), 0), Box::new(List::Nil)));
    let g = Function { params: List::Cons((BA, Ty::I32), Box::new(List::Cons((BB, Ty::U32), Box::new(List::Nil)))), ..f(Expr::Bin(BinOp::BitAnd, b(Expr::Name(BA)), b(Expr::Int(1)))) };
    assert_eq!(refusal_of(&translate_function(&g, &List::Nil, &List::Nil)), Refusal::SignedBits(19));
}

/// The contract parser reads a cast, `&` and `|` between two values, and keeps `|e|` as the absolute value, decision 0175.
#[test]
fn the_parser_reads_casts_and_bits() {
    let (x, y) = (384, 385);
    let cast = parse_contract(&vec![Tok::Cast(Ty::U32), Tok::LParen, Tok::Ident(x), Tok::RParen], 4);
    assert_eq!(cast, Ok(Expr::StaticCast(Ty::U32, b(Expr::Name(x)))));
    let and = parse_contract(&vec![Tok::Ident(x), Tok::Op(BinOp::BitAnd), Tok::Ident(y)], 4);
    assert_eq!(and, Ok(Expr::Bin(BinOp::BitAnd, b(Expr::Name(x)), b(Expr::Name(y)))));
    let or = parse_contract(&vec![Tok::Ident(x), Tok::Bar, Tok::Ident(y)], 4);
    assert_eq!(or, Ok(Expr::Bin(BinOp::BitOr, b(Expr::Name(x)), b(Expr::Name(y)))));
    let abs = parse_contract(&vec![Tok::Bar, Tok::Ident(x), Tok::Bar, Tok::Op(BinOp::Add), Tok::Bar, Tok::Ident(y), Tok::Bar], 4);
    assert_eq!(abs, Ok(Expr::Bin(BinOp::Add, b(Expr::Abs(b(Expr::Name(x)))), b(Expr::Abs(b(Expr::Name(y)))))));
}

/// `a.count()` of an int64 in a contract is `a`, as a duration in milliseconds is its count, decision 0175.
#[test]
fn the_count_of_a_duration_is_its_value() {
    let req = Expr::Bin(BinOp::Ge, b(Expr::MApply(b(Expr::Name(BA)), COUNT_NAME, Box::new(List::Nil))), b(Expr::Int(0)));
    let conds = List::Cons((CondKind::Requires, req, 19, names(&[BA])), Box::new(List::Nil));
    let f = Function { name: 386, line: 20, params: List::Cons((BA, Ty::I64), Box::new(List::Nil)), ret: Ty::Void, trusted: true, conds, body: List::Nil };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Ge, Box::new(DExpr::AsInt(Box::new(DExpr::Var(BA)))), Box::new(DExpr::Lit(0)));
    assert_eq!(strip_conds(m.requires), List::Cons((want, 0), Box::new(List::Nil)));
}

/// A std::array as a result has its length as an ensures line, and `return {a, b, c};` is the sequence of the values. A list of
/// another length is refused, decision 0175.
#[test]
fn an_array_result_is_a_fixed_sequence() {
    let three = Ty::Seq(Scalar::I32, Extent::Fixed(3));
    let list = |vs: &[u64]| Expr::List(Box::new(vs.iter().rev().fold(List::Nil, |rest, v| List::Cons(b(Expr::Lit(*v, Ty::I32)), Box::new(rest)))));
    let f = |vs: &[u64]| Function { name: 387, line: 20, params: List::Nil, ret: three, trusted: false, conds: List::Nil, body: one(Stmt::Return(list(vs), 21)) };
    let Model::Full(m) = translate_function(&f(&[10, 20, 30]), &List::Nil, &List::Nil) else { panic!("a full model") };
    let lits = [10, 20, 30].iter().rev().fold(List::Nil, |rest, v| List::Cons(lit32(*v), Box::new(rest)));
    assert_eq!(strip(m.body), List::Cons((Box::new(DStmt::Return(DExpr::SeqLit(Box::new(lits)))), 0), Box::new(List::Nil)));
    let len = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Result))), Box::new(DExpr::Lit(3)));
    assert!(matches!(&m.ensures, List::Cons((d, _), _) if *d == len), "{:?}", m.ensures);
    assert_eq!(refusal_of(&translate_function(&f(&[10, 20]), &List::Nil, &List::Nil)), Refusal::BraceLen(2, 3, 21));
}

const FILE_ENTRY: u32 = 400;
const SATKEY: u32 = 401;
const HAS: u32 = 402;
const KHAS: u32 = 403;
const FLAGS: u32 = 404;
const FLAG: u32 = 405;
const TWICE: u32 = 406;
const KTWICE: u32 = 407;
const FBUMP: u32 = 408;
const KFBUMP: u32 = 409;
const GFREE: u32 = 410;
const KGFREE: u32 = 411;

/// The contract lines hold `d`.
fn dconds_hold(cs: &DConds, d: &DExpr) -> bool {
    match cs {
        List::Nil => false,
        List::Cons((x, _), rest) => x == d || dconds_hold(rest, d),
    }
}

fn two(a: (u32, Ty), c: (u32, Ty)) -> Params {
    List::Cons(a, Box::new(List::Cons(c, Box::new(List::Nil))))
}

/// The free functions of a file under the one entry of the file, decision 0176.
fn file_table(ms: Members) -> Structs {
    List::Cons((FILE_ENTRY, (0, List::Nil, ms)), Box::new(List::Nil))
}

fn has_fn() -> Function {
    let and = Expr::Bits(BinOp::BitAnd, b(read(FLAGS, Ty::U32)), b(read(FLAG, Ty::U32)), Ty::U32);
    let body = one(Stmt::Return(Expr::Bin(BinOp::Eq, b(and), b(read(FLAG, Ty::U32))), 8));
    Function { name: KHAS, line: 7, params: two((FLAGS, Ty::U32), (FLAG, Ty::U32)), ret: Ty::Bool, trusted: false, conds: List::Nil, body }
}

/// A free function with one return and no call has a twin when the file lists it, and a contract calls the twin by its name,
/// decision 0176.
#[test]
fn a_free_function_has_a_twin_when_the_file_lists_it() {
    let ms = List::Cons(
        (HAS, (KHAS, Some((Ty::Bool, two((FLAGS, Ty::U32), (FLAG, Ty::U32)))))),
        Box::new(List::Cons((TWICE, (KTWICE, Some((Ty::I32, List::Cons((X, Ty::I32), Box::new(List::Nil)))))), Box::new(List::Nil))),
    );
    let table = file_table(ms);
    let Model::Full(m) = translate_function(&has_fn(), &List::Nil, &table) else { panic!("a full model") };
    let and = DExpr::Conv(DTy::UInt32, Box::new(DExpr::BitOp(BinOp::BitAnd, Box::new(DExpr::AsInt(Box::new(DExpr::Var(FLAGS)))), Box::new(DExpr::AsInt(Box::new(DExpr::Var(FLAG)))))));
    assert_eq!(m.function, Some(DExpr::Bin(BinOp::Eq, Box::new(and), Box::new(DExpr::Var(FLAG)))));
    let args = List::Cons(DExpr::Var(FLAGS), Box::new(List::Cons(DExpr::Var(FLAG), Box::new(List::Nil))));
    let link = DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(KHAS, Box::new(args))));
    assert!(dconds_hold(&m.ensures, &link), "{:?}", m.ensures);
    // A contract of another function calls the twin with its arguments.
    let ens = Expr::Apply(HAS, Box::new(List::Cons(b(Expr::Result), Box::new(List::Cons(b(Expr::Name(FLAG)), Box::new(List::Nil))))));
    let grant = Function { name: 412, line: 24, params: two((FLAGS, Ty::U32), (FLAG, Ty::U32)), ret: Ty::U32, trusted: true, conds: List::Cons((CondKind::Ensures, ens, 23, names(&[FLAGS, FLAG])), Box::new(List::Nil)), body: List::Nil };
    let Model::Full(m) = translate_function(&grant, &List::Nil, &table) else { panic!("a full model") };
    // Each argument is an exact integer, converted to the type of its parameter, as decision 0095 has it.
    let conv = |d: DExpr| DExpr::Conv(DTy::UInt32, Box::new(DExpr::AsInt(Box::new(d))));
    let args = List::Cons(conv(DExpr::Result), Box::new(List::Cons(conv(DExpr::Var(FLAG)), Box::new(List::Nil))));
    assert_eq!(strip_conds(m.ensures), List::Cons((DExpr::FCall(KHAS, Box::new(args)), 0), Box::new(List::Nil)));
    // A literal argument converts to the type of the parameter.
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(TWICE, Box::new(List::Cons(b(Expr::Int(3)), Box::new(List::Nil))))));
    let six = Function { name: 413, line: 41, params: List::Nil, ret: Ty::I32, trusted: true, conds: List::Cons((CondKind::Ensures, ens, 40, names(&[])), Box::new(List::Nil)), body: List::Nil };
    let Model::Full(m) = translate_function(&six, &List::Nil, &table) else { panic!("a full model") };
    let call = DExpr::FCall(KTWICE, Box::new(List::Cons(DExpr::Conv(DTy::Int32, Box::new(DExpr::Lit(3))), Box::new(List::Nil))));
    let want = DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(DExpr::AsInt(Box::new(call))));
    assert_eq!(strip_conds(m.ensures), List::Cons((want, 0), Box::new(List::Nil)));
    // A free function that the file does not list has no twin.
    let Model::Full(m) = translate_function(&has_fn(), &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.function, None);
}

/// A contract that calls a free function with no twin is refused, and a body that calls a free function gives no twin,
/// decision 0176.
#[test]
fn a_free_function_with_no_twin_is_refused_in_a_contract() {
    let table = file_table(List::Cons((FBUMP, (KFBUMP, None)), Box::new(List::Nil)));
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Apply(FBUMP, Box::new(List::Cons(b(Expr::Name(X)), Box::new(List::Nil))))));
    let next = Function { name: 414, line: 27, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: true, conds: List::Cons((CondKind::Ensures, ens, 26, names(&[X])), Box::new(List::Nil)), body: List::Nil };
    assert_eq!(refusal_of(&translate_function(&next, &List::Nil, &table)), Refusal::NotPure(FBUMP, 26));
    // `return g(x)` of a free `g` is a call, so the body gives no twin.
    let g = Function { name: KGFREE, line: 3, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(read(X, Ty::I32), 4)) };
    let call = Expr::Call(KGFREE, GFREE, Box::new(List::Cons(b(read(X, Ty::I32)), Box::new(List::Nil))), 7);
    let f = Function { name: 415, line: 6, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(call, 7)) };
    let ms = List::Cons((GFREE, (KGFREE, Some((Ty::I32, List::Cons((X, Ty::I32), Box::new(List::Nil)))))), Box::new(List::Cons((416, (415, None)), Box::new(List::Nil))));
    let all = fns(vec![g]);
    let Model::Full(m) = translate_function(&f, &all, &file_table(ms)) else { panic!("a full model") };
    assert_eq!(m.function, None);
}

const WY: u32 = 420;
const UNDER: u32 = 421;
const WTAKE: u32 = 422;

fn step(n: u32, t: Ty, up: bool, prefix: bool) -> Expr {
    Expr::Step(n, t, up, prefix)
}

fn pres(v: Vec<DPre>) -> DCalls {
    v.into_iter().rev().fold(List::Nil, |rest, p| List::Cons(p, Box::new(rest)))
}

fn block(v: Vec<DStmt>) -> DStmt {
    DStmt::Block(Box::new(stmts(v)))
}

fn gt0(d: DExpr) -> DExpr {
    DExpr::Bin(BinOp::Gt, Box::new(d), Box::new(lit32(0)))
}

/// `int32_t f(int32_t& x, int32_t& y)` with modifies x, y, and a body of `body`.
fn writer(body: Stmts) -> Function {
    let ps = List::Cons((X, mut32()), Box::new(List::Cons((WY, mut32()), Box::new(List::Nil))));
    Function { name: 423, line: 10, params: ps, ret: Ty::I32, trusted: false, conds: modifies(&[X, WY], &[X, WY], List::Nil), body }
}

fn the_body(m: Model) -> DStmt {
    let Model::Full(m) = m else { panic!("a full model: {m:?}") };
    let List::Cons((s, _), _) = strip(m.body) else { panic!("a body") };
    *s
}

/// `x++` and `++x` inside an expression write before the statement into a temporary, decision 0177. A by-value parameter cannot
/// be written.
#[test]
fn a_step_in_an_expression_writes_first() {
    let ret = |e: Expr| one(Stmt::Return(e, 11));
    let post = the_body(translate_function(&writer(ret(step(X, mut32(), true, false))), &List::Nil, &List::Nil));
    assert_eq!(post, DStmt::Pre(pres(vec![DPre::Step(0, DTy::Int32, X, true, false, true)]), Box::new(DStmt::Return(DExpr::Temp(0)))));
    let pre = the_body(translate_function(&writer(ret(step(X, mut32(), true, true))), &List::Nil, &List::Nil));
    assert_eq!(pre, DStmt::Pre(pres(vec![DPre::Step(0, DTy::Int32, X, true, true, true)]), Box::new(DStmt::Return(DExpr::Temp(0)))));
    // A local: int32_t a = 0; return a--;
    let body = List::Cons(Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(0, Ty::I32), 11)), Box::new(one(Stmt::Return(step(A, Ty::I32, false, false), 12))));
    let Model::Full(m) = translate_function(&writer(body), &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("a body") };
    let List::Cons((second, _), _) = *rest else { panic!("two statements") };
    assert_eq!(*second, DStmt::Pre(pres(vec![DPre::Step(0, DTy::Int32, A, false, false, false)]), Box::new(DStmt::Return(DExpr::Temp(0)))));
    // A by-value parameter: int32_t g(int32_t x) { return x++; }
    let g = Function { name: 424, line: 10, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: ret(step(X, Ty::I32, true, false)) };
    assert_eq!(bare_refusal(translate_function(&g, &List::Nil, &List::Nil)), Refusal::WriteParam(X, 11));
}

/// A call that writes a value back runs before the statement into a temporary, and writes back its places, decision 0177.
#[test]
fn a_call_that_writes_lifts_into_a_temporary() {
    let all = fns(vec![next_fn()]);
    let body = one(Stmt::Return(Expr::Bin(BinOp::Gt, b(call(NEXT, vec![Expr::Var(X, mut32())], 11)), b(Expr::Lit(0, Ty::I32))), 11));
    let f = Function { ret: Ty::Bool, ..writer(body) };
    let got = the_body(translate_function(&f, &all, &List::Nil));
    let pre = pres(vec![DPre::Update(0, DTy::Int32, objs(&[Obj::Out(X)]), NEXT, dargs(vec![DExpr::Out(X)]))]);
    assert_eq!(got, DStmt::Pre(pre, Box::new(DStmt::Return(gt0(DExpr::Temp(0))))));
}

/// A `return` with a call on the right of && or || or in a branch of ?: becomes an if, so the call runs only when C++ runs
/// it. A pure call there takes the same path, decision 0177.
#[test]
fn a_call_on_the_right_of_and_becomes_an_if() {
    let under = Function { name: UNDER, line: 3, params: List::Cons((A, Ty::I32), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, body: one(Stmt::Return(Expr::Bool(true), 4)) };
    let all = fns(vec![next_fn(), under]);
    let next = |v: u32| Expr::Bin(BinOp::Gt, b(call(NEXT, vec![Expr::Var(v, mut32())], 11)), b(Expr::Lit(0, Ty::I32)));
    let upd = |t: u32, v: u32| DPre::Update(t, DTy::Int32, objs(&[Obj::Out(v)]), NEXT, dargs(vec![DExpr::Out(v)]));
    let set = |t: u32, d: DExpr| DStmt::AssignTemp(t, d);
    let ret_bool = |e: Expr| Function { ret: Ty::Bool, ..writer(one(Stmt::Return(e, 11))) };
    // return next(x) > 0 && next(y) > 0;
    let and = Expr::Bin(BinOp::And, b(next(X)), b(next(WY)));
    let got = the_body(translate_function(&ret_bool(and), &all, &List::Nil));
    let right = List::Cons((Box::new(DStmt::Pre(pres(vec![upd(2, WY)]), Box::new(set(0, gt0(DExpr::Temp(2)))))), 0), Box::new(List::Nil));
    let want = block(vec![
        DStmt::DeclTemp(0, DTy::Bool),
        DStmt::Pre(pres(vec![upd(1, X)]), Box::new(set(0, gt0(DExpr::Temp(1))))),
        DStmt::If(DExpr::Temp(0), Box::new(right), Box::new(List::Nil)),
        DStmt::Return(DExpr::Temp(0)),
    ]);
    assert_eq!(got, want);
    // return next(x) > 0 || next(y) > 0; the right side runs when the left is false.
    let or = Expr::Bin(BinOp::Or, b(next(X)), b(next(WY)));
    let DStmt::Block(got) = the_body(translate_function(&ret_bool(or), &all, &List::Nil)) else { panic!("a block") };
    let List::Cons(_, rest) = *got else { panic!("statements") };
    let List::Cons(_, rest) = *rest else { panic!("statements") };
    let List::Cons((cond, _), _) = *rest else { panic!("statements") };
    assert!(matches!(&*cond, DStmt::If(DExpr::Not(t), _, _) if **t == DExpr::Temp(0)), "{cond:?}");
    // return take ? next(x) : 0; each branch returns its value.
    let pick = Expr::Cond(b(Expr::Var(WTAKE, Ty::Bool)), b(call(NEXT, vec![Expr::Var(X, mut32())], 11)), b(Expr::Lit(0, Ty::I32)));
    let ps = List::Cons((WTAKE, Ty::Bool), Box::new(List::Cons((X, mut32()), Box::new(List::Nil))));
    let f = Function { name: 426, line: 10, params: ps, ret: Ty::I32, trusted: false, conds: modifies(&[X], &[WTAKE, X], List::Nil), body: one(Stmt::Return(pick, 11)) };
    let got = the_body(translate_function(&f, &all, &List::Nil));
    let then = List::Cons((Box::new(DStmt::Pre(pres(vec![upd(0, X)]), Box::new(DStmt::Return(DExpr::Temp(0))))), 0), Box::new(List::Nil));
    let other = List::Cons((Box::new(DStmt::Return(lit32(0))), 0), Box::new(List::Nil));
    assert_eq!(got, block(vec![DStmt::If(DExpr::Var(WTAKE), Box::new(then), Box::new(other))]));
    // return a > 0 && under_ten(a); a pure call on the right is no call out of place.
    let small = Expr::Bin(BinOp::And, b(Expr::Bin(BinOp::Gt, b(read(A, Ty::I32)), b(Expr::Lit(0, Ty::I32)))), b(call(UNDER, vec![read(A, Ty::I32)], 11)));
    let f = Function { name: 425, line: 10, params: List::Cons((A, Ty::I32), Box::new(List::Nil)), ret: Ty::Bool, trusted: false, conds: List::Nil, body: one(Stmt::Return(small, 11)) };
    let got = the_body(translate_function(&f, &all, &List::Nil));
    let right = List::Cons((Box::new(DStmt::Pre(pres(vec![DPre::Call(1, DTy::Bool, UNDER, dargs(vec![DExpr::Var(A)]))]), Box::new(set(0, DExpr::Temp(1))))), 0), Box::new(List::Nil));
    let want = block(vec![
        DStmt::DeclTemp(0, DTy::Bool),
        set(0, gt0(DExpr::Var(A))),
        DStmt::If(DExpr::Temp(0), Box::new(right), Box::new(List::Nil)),
        DStmt::Return(DExpr::Temp(0)),
    ]);
    assert_eq!(got, want);
}

/// Two writes where C++ fixes no order, or a write and a read of one name, are refused. The two sides of && are two regions,
/// decision 0177.
#[test]
fn two_writes_or_a_write_and_a_read_are_refused() {
    let all = fns(vec![next_fn()]);
    let ret = |e: Expr| writer(one(Stmt::Return(e, 11)));
    let add = |a: Expr, c: Expr| Expr::Bin(BinOp::Add, b(a), b(c));
    let two = add(step(X, mut32(), true, false), step(WY, mut32(), true, false));
    assert_eq!(bare_refusal(translate_function(&ret(two), &all, &List::Nil)), Refusal::TwoWrites(11));
    let read_too = add(step(X, mut32(), true, false), read(X, mut32()));
    assert_eq!(bare_refusal(translate_function(&ret(read_too), &all, &List::Nil)), Refusal::WriteRead(X, 11));
    let call_read = add(call(NEXT, vec![Expr::Var(X, mut32())], 11), read(X, mut32()));
    assert_eq!(bare_refusal(translate_function(&ret(call_read), &all, &List::Nil)), Refusal::WriteRead(X, 11));
    let gt = |e: Expr| Expr::Bin(BinOp::Gt, b(e), b(Expr::Lit(0, Ty::I32)));
    let regions = Expr::Bin(BinOp::And, b(gt(step(X, mut32(), true, false))), b(gt(step(WY, mut32(), true, false))));
    let f = Function { ret: Ty::Bool, ..ret(regions) };
    assert!(matches!(translate_function(&f, &all, &List::Nil), Model::Full(_)));
}

/// A write in the condition of a loop has no rule, and a call there keeps the refusal of decision 0104, decision 0177.
#[test]
fn a_write_in_a_loop_condition_is_refused() {
    let all = fns(vec![next_fn()]);
    let lt = |e: Expr| Expr::Bin(BinOp::Lt, b(e), b(Expr::Lit(10, Ty::I32)));
    let looped = |c: Expr| writer(List::Cons(Box::new(Stmt::While(c, Box::new(List::Nil), Box::new(List::Nil), 12)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 14)))));
    assert_eq!(bare_refusal(translate_function(&looped(lt(step(X, mut32(), true, false))), &all, &List::Nil)), Refusal::LoopWrite(12));
    assert_eq!(bare_refusal(translate_function(&looped(lt(call(NEXT, vec![Expr::Var(X, mut32())], 12))), &all, &List::Nil)), Refusal::Place(12));
}

const GUARD: u32 = 430;
const KCTOR: u32 = 431;
const KDTOR: u32 = 432;
const KHANDLE: u32 = 433;
const HANDLE_N: u32 = 434;
const HANDLE_F: u32 = 435;
const GG: u32 = 436;
const GB: u32 = 437;
const GN: u32 = 438;
const GTAKE: u32 = 439;
const QUIET: u32 = 440;
const KQCTOR: u32 = 441;
const KQDTOR: u32 = 442;
const GO: u32 = 443;

fn ps(v: &[(u32, Ty)]) -> Params {
    v.iter().rev().fold(List::Nil, |rest, p| List::Cons(*p, Box::new(rest)))
}

fn mods(line: u32, decl: &[u32]) -> Conds {
    List::Cons((CondKind::Modifies, Expr::Name(GO), line, names(decl)), Box::new(List::Nil))
}

/// A guard with a constructor and a destructor that each write the global `open`, and a const member `handle()`, decision 0178.
fn guard_fns() -> Fns {
    let ctor = Function { name: KCTOR, line: 27, params: ps(&[(GO, mut32())]), ret: Ty::This(GUARD), trusted: true, conds: mods(25, &[GO]), body: List::Nil };
    let dtor = Function { name: KDTOR, line: 32, params: ps(&[(THIS, Ty::ThisMut(GUARD)), (GO, mut32())]), ret: Ty::Void, trusted: true, conds: mods(30, &[THIS, GO]), body: List::Nil };
    let handle = Function { name: KHANDLE, line: 35, params: ps(&[(THIS, Ty::This(GUARD))]), ret: Ty::I32, trusted: true, conds: List::Nil, body: List::Nil };
    let qctor = Function { name: KQCTOR, line: 42, params: List::Nil, ret: Ty::This(QUIET), trusted: true, conds: List::Nil, body: List::Nil };
    let qdtor = Function { name: KQDTOR, line: 43, params: ps(&[(THIS, Ty::ThisMut(QUIET))]), ret: Ty::Void, trusted: false, conds: List::Nil, body: List::Nil };
    fns(vec![ctor, dtor, handle, qctor, qdtor])
}

fn guard_table() -> Structs {
    let ms = List::Cons(
        (DTOR_NAME, (KDTOR, None)),
        Box::new(List::Cons((HANDLE_N, (KHANDLE, Some((Ty::I32, ps(&[(THIS, Ty::This(GUARD))]))))), Box::new(List::Nil))),
    );
    let guard = (GUARD, (22, ps(&[(HANDLE_F, Ty::I32)]), ms));
    let quiet = (QUIET, (39, ps(&[(GN, Ty::I32)]), List::Cons((DTOR_NAME, (KQDTOR, None)), Box::new(List::Nil))));
    List::Cons(guard, Box::new(List::Cons(quiet, Box::new(List::Nil))))
}

fn guard_local(v: u32, line: u32) -> Stmt {
    Stmt::Local(v, Ty::Struct(GUARD), call(KCTOR, vec![Expr::Var(GO, mut32())], line), line)
}

fn guard_user(body: Stmts) -> Function {
    Function { name: 444, line: 44, params: ps(&[(GO, mut32())]), ret: Ty::I32, trusted: false, conds: mods(42, &[GO]), body }
}

fn stmts(v: Vec<DStmt>) -> DStmts {
    v.into_iter().rev().fold(List::Nil, |rest, d| List::Cons((Box::new(d), 0), Box::new(rest)))
}

fn made(v: u32) -> DStmt {
    DStmt::LocalUpdate(v, DTy::Struct(GUARD), objs(&[Obj::Out(GO)]), KCTOR, dargs(vec![DExpr::Out(GO)]))
}

fn dies(v: u32) -> DStmt {
    DStmt::Update(objs(&[Obj::Local(v), Obj::Out(GO)]), KDTOR, dargs(vec![DExpr::Var(v), DExpr::Out(GO)]))
}

/// The statements of a `return` with live locals: the value, then each destructor, then the exit.
fn dying(value: DStmt, ds: Vec<DStmt>) -> DStmt {
    block(vec![value, DStmt::Dtors(Box::new(stmts(ds))), DStmt::Exit])
}

/// A local of a struct with a destructor dies before a return, after the value of the return. The destructor takes the
/// global back, decision 0178.
#[test]
fn a_destructor_runs_before_a_return() {
    let body = List::Cons(Box::new(guard_local(GG, 45)), Box::new(one(Stmt::Return(call(KHANDLE, vec![read(GG, Ty::Struct(GUARD))], 46), 46))));
    let Model::Full(m) = translate_function(&guard_user(body), &guard_fns(), &guard_table()) else { panic!("a full model") };
    let value = DStmt::Pre(pres(vec![DPre::Call(0, DTy::Int32, KHANDLE, dargs(vec![DExpr::Var(GG)]))]), Box::new(DStmt::SetResult(DExpr::Temp(0))));
    assert_eq!(strip(m.body), stmts(vec![made(GG), dying(value, vec![dies(GG)])]));
}

/// Two locals die in the reverse order, and a local of a bare block dies at its end, decision 0178.
#[test]
fn locals_die_in_reverse_order_and_at_the_end_of_their_block() {
    let inner = List::Cons(Box::new(guard_local(GB, 57)), Box::new(one(Stmt::Assign(GN, read(GO, mut32()), 58))));
    let body = List::Cons(
        Box::new(guard_local(GG, 54)),
        Box::new(List::Cons(
            Box::new(Stmt::Local(GN, Ty::I32, Expr::Lit(0, Ty::I32), 55)),
            Box::new(List::Cons(Box::new(Stmt::Block(Box::new(inner), 56)), Box::new(one(Stmt::Return(read(GN, Ty::I32), 60))))),
        )),
    );
    let Model::Full(m) = translate_function(&guard_user(body), &guard_fns(), &guard_table()) else { panic!("a full model") };
    let scope = DStmt::Scope(Box::new(stmts(vec![made(GB), DStmt::Assign(GN, DExpr::Out(GO)), DStmt::Dtors(Box::new(stmts(vec![dies(GB)])))])));
    let want = stmts(vec![made(GG), DStmt::Local(GN, DTy::Int32, lit32(0)), scope, dying(DStmt::SetResult(DExpr::Var(GN)), vec![dies(GG)])]);
    assert_eq!(strip(m.body), want);
    // Two locals of one block: the later one dies first.
    let body = List::Cons(Box::new(guard_local(GG, 54)), Box::new(List::Cons(Box::new(guard_local(GB, 55)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 56))))));
    let Model::Full(m) = translate_function(&guard_user(body), &guard_fns(), &guard_table()) else { panic!("a full model") };
    let List::Cons(_, rest) = strip(m.body) else { panic!("a body") };
    let List::Cons(_, rest) = *rest else { panic!("a body") };
    let List::Cons((last, _), _) = *rest else { panic!("a body") };
    assert_eq!(*last, dying(DStmt::SetResult(lit32(0)), vec![dies(GB), dies(GG)]));
}

/// A return inside an if destroys the locals of the enclosing blocks, and a branch that returns gets no destructor at its end,
/// decision 0178.
#[test]
fn a_return_in_a_branch_destroys_the_enclosing_locals() {
    let then = one(Stmt::Return(Expr::Lit(1, Ty::I32), 70));
    let body = List::Cons(
        Box::new(guard_local(GG, 68)),
        Box::new(List::Cons(Box::new(Stmt::If(read(GTAKE, Ty::Bool), Box::new(then), Box::new(List::Nil), 69)), Box::new(one(Stmt::Return(Expr::Lit(2, Ty::I32), 72))))),
    );
    let f = Function { params: ps(&[(GTAKE, Ty::Bool), (GO, mut32())]), conds: mods(65, &[GTAKE, GO]), ..guard_user(body) };
    let Model::Full(m) = translate_function(&f, &guard_fns(), &guard_table()) else { panic!("a full model") };
    let branch = stmts(vec![dying(DStmt::SetResult(lit32(1)), vec![dies(GG)])]);
    let want = stmts(vec![made(GG), DStmt::If(DExpr::Var(GTAKE), Box::new(branch), Box::new(List::Nil)), dying(DStmt::SetResult(lit32(2)), vec![dies(GG)])]);
    assert_eq!(strip(m.body), want);
}

/// A copy of a struct with a destructor has no rule: a return of a local, a local made from a local, and a parameter by value,
/// decision 0178.
#[test]
fn a_copy_of_a_struct_with_a_destructor_is_refused() {
    let ret = List::Cons(Box::new(guard_local(GG, 25)), Box::new(one(Stmt::Return(read(GG, Ty::Struct(GUARD)), 26))));
    let f = Function { ret: Ty::Struct(GUARD), ..guard_user(ret) };
    assert_eq!(refusal_of(&translate_function(&f, &guard_fns(), &guard_table())), Refusal::Copy(26));
    let copy = List::Cons(
        Box::new(guard_local(GG, 25)),
        Box::new(List::Cons(Box::new(Stmt::Local(GB, Ty::Struct(GUARD), read(GG, Ty::Struct(GUARD)), 27)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 28))))),
    );
    assert_eq!(refusal_of(&translate_function(&guard_user(copy), &guard_fns(), &guard_table())), Refusal::Copy(27));
    let by_value = Function { name: 445, line: 30, params: ps(&[(GG, Ty::Struct(GUARD))]), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 31)) };
    assert_eq!(refusal_of(&translate_function(&by_value, &guard_fns(), &guard_table())), Refusal::Copy(30));
}

/// A local of a struct whose destructor has no contract has no rule, decision 0178.
#[test]
fn a_destructor_with_no_contract_is_refused() {
    let body = List::Cons(Box::new(Stmt::Local(GG, Ty::Struct(QUIET), call(KQCTOR, vec![], 50), 50)), Box::new(one(Stmt::Return(Expr::Lit(1, Ty::I32), 51))));
    let f = Function { name: 446, line: 49, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    assert_eq!(refusal_of(&translate_function(&f, &guard_fns(), &guard_table())), Refusal::NoDtorContract(50));
}

/// A local of an if branch or of a loop body dies at the end of the branch or the body. A `return;` and the end of a void
/// function destroy the live locals, decision 0178.
#[test]
fn a_destructor_runs_at_the_end_of_a_branch_a_loop_body_and_a_void_function() {
    // Each name is declared once in a function, decision 0058, so the branch and the loop hold two guards.
    let inner = |v: u32, line: u32| Box::new(one(guard_local(v, line)));
    let body = List::Cons(
        Box::new(guard_local(GG, 68)),
        Box::new(List::Cons(
            Box::new(Stmt::If(read(GTAKE, Ty::Bool), Box::new(one(Stmt::Exit(70))), inner(GB, 71), 69)),
            Box::new(one(Stmt::While(read(GTAKE, Ty::Bool), Box::new(List::Nil), inner(GN, 73), 72))),
        )),
    );
    let f = Function { params: ps(&[(GTAKE, Ty::Bool), (GO, mut32())]), ret: Ty::Void, conds: mods(65, &[GTAKE, GO]), ..guard_user(body) };
    let Model::Full(m) = translate_function(&f, &guard_fns(), &guard_table()) else { panic!("a full model") };
    let own = |v: u32| Box::new(stmts(vec![made(v), DStmt::Dtors(Box::new(stmts(vec![dies(v)])))]));
    let exit = stmts(vec![block(vec![DStmt::Dtors(Box::new(stmts(vec![dies(GG)]))), DStmt::Exit])]);
    let want = stmts(vec![made(GG), DStmt::If(DExpr::Var(GTAKE), Box::new(exit), own(GB)), DStmt::While(DExpr::Var(GTAKE), List::Nil, List::Nil, own(GN)), DStmt::Dtors(Box::new(stmts(vec![dies(GG)])))]);
    assert_eq!(strip(m.body), want);
}

/// A return that runs a call only sometimes, decision 0177, sets the result in each branch, and then the locals die,
/// decision 0178.
#[test]
fn a_lowered_return_sets_the_result_before_the_locals_die() {
    let pick = Expr::Cond(b(read(GTAKE, Ty::Bool)), b(call(KHANDLE, vec![read(GG, Ty::Struct(GUARD))], 67)), b(Expr::Lit(1, Ty::I32)));
    let body = List::Cons(Box::new(guard_local(GG, 66)), Box::new(one(Stmt::Return(pick, 67))));
    let f = Function { params: ps(&[(GTAKE, Ty::Bool), (GO, mut32())]), conds: mods(63, &[GTAKE, GO]), ..guard_user(body) };
    let Model::Full(m) = translate_function(&f, &guard_fns(), &guard_table()) else { panic!("a full model") };
    let then = stmts(vec![DStmt::Pre(pres(vec![DPre::Call(0, DTy::Int32, KHANDLE, dargs(vec![DExpr::Var(GG)]))]), Box::new(DStmt::SetResult(DExpr::Temp(0))))]);
    let other = stmts(vec![DStmt::SetResult(lit32(1))]);
    let want = stmts(vec![made(GG), block(vec![DStmt::If(DExpr::Var(GTAKE), Box::new(then), Box::new(other)), DStmt::Dtors(Box::new(stmts(vec![dies(GG)]))), DStmt::Exit])]);
    assert_eq!(strip(m.body), want);
}

/// The body of a constructor of a struct with a destructor builds the struct, and that is the result, no temporary, decision
/// 0178.
#[test]
fn a_constructor_of_a_struct_with_a_destructor_builds_its_result() {
    let built = Expr::Construct(GUARD, Box::new(List::Cons(b(Expr::Lit(0, Ty::I32)), Box::new(List::Nil))));
    let ctor = Function { name: 447, line: 10, params: List::Nil, ret: Ty::This(GUARD), trusted: false, conds: List::Nil, body: one(Stmt::Return(built, 10)) };
    let Model::Full(m) = translate_function(&ctor, &guard_fns(), &guard_table()) else { panic!("a full model") };
    let want = DStmt::Return(DExpr::Ctor(GUARD, Box::new(List::Cons(lit32(0), Box::new(List::Nil)))));
    assert_eq!(strip(m.body), stmts(vec![want]));
}

/// A local vector of a struct with a destructor is a copy, also when it starts empty, decision 0178.
#[test]
fn a_local_vector_of_a_struct_with_a_destructor_is_refused() {
    let body = List::Cons(Box::new(Stmt::Local(GB, Ty::Vec(Scalar::Struct(GUARD)), Expr::EmptyVec, 50)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 51))));
    let f = Function { name: 448, line: 49, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    assert_eq!(refusal_of(&translate_function(&f, &guard_fns(), &guard_table())), Refusal::Copy(50));
}

/// An assignment from a call that gives a struct with a destructor assigns a temporary, which dies at once, decision 0178.
#[test]
fn an_assignment_of_a_temporary_with_a_destructor_is_refused() {
    let body = List::Cons(
        Box::new(guard_local(GG, 45)),
        Box::new(List::Cons(Box::new(Stmt::Assign(GG, call(450, vec![], 46), 46)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 47))))),
    );
    // `make()` writes nothing, so no other rule refuses the assignment first.
    let make = Function { name: 450, line: 40, params: List::Nil, ret: Ty::Struct(GUARD), trusted: true, conds: List::Nil, body: List::Nil };
    let all = List::Cons(Box::new(make), Box::new(guard_fns()));
    assert_eq!(refusal_of(&translate_function(&guard_user(body), &all, &guard_table())), Refusal::Copy(46));
}

/// A call that gives no value has no place inside an expression, decision 0177. The core says so, whatever the callee writes.
#[test]
fn a_call_that_gives_no_value_inside_an_expression_is_out_of_place() {
    let vf = Function { name: 451, line: 20, params: List::Nil, ret: Ty::Void, trusted: true, conds: List::Nil, body: List::Nil };
    let all = fns(vec![vf]);
    let e = Expr::Bin(BinOp::Add, b(call(451, vec![], 30)), b(Expr::Lit(1, Ty::I32)));
    assert_eq!(bare_refusal(translate_function(&succ(e), &all, &List::Nil)), Refusal::Place(30));
}

/// A local std::array from a brace list of its length is a local of the sequence of the values, and a write to an element is a new
/// value of the local. A list of another length is refused, decision 0184.
#[test]
fn a_local_array_from_a_brace_list_is_a_sequence() {
    let three = Ty::Seq(Scalar::I32, Extent::Fixed(3));
    let list = |vs: &[u64]| Expr::List(Box::new(vs.iter().rev().fold(List::Nil, |rest, v| List::Cons(b(Expr::Lit(*v, Ty::I32)), Box::new(rest)))));
    let f = |vs: &[u64]| {
        let body = List::Cons(
            Box::new(Stmt::Local(X, three, list(vs), 21)),
            Box::new(List::Cons(Box::new(Stmt::SetIndex(X, Expr::Lit(0, Ty::U64), Expr::Lit(5, Ty::I32), 22)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 23))))),
        );
        Function { name: 452, line: 20, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body }
    };
    let Model::Full(m) = translate_function(&f(&[10, 20, 30]), &List::Nil, &List::Nil) else { panic!("a full model") };
    let lits = [10, 20, 30].iter().rev().fold(List::Nil, |rest, v| List::Cons(lit32(*v), Box::new(rest)));
    let List::Cons((first, _), rest) = strip(m.body) else { panic!("a body") };
    assert!(matches!(&*first, DStmt::Local(v, _, DExpr::SeqLit(l)) if *v == X && **l == lits), "{first:?}");
    let List::Cons((second, _), _) = *rest else { panic!("a write") };
    assert!(matches!(&*second, DStmt::Assign(v, DExpr::SetAt(..)) if *v == X), "{second:?}");
    assert_eq!(refusal_of(&translate_function(&f(&[10, 20]), &List::Nil, &List::Nil)), Refusal::BraceLen(2, 3, 21));
}

/// `v(n, x)` of a local vector is a sequence of n copies of x. A move of a local vector gives the new local its value, then leaves
/// the source with any value, decision 0185.
#[test]
fn a_local_vector_from_a_fill_and_from_a_move() {
    let vec = Ty::Vec(Scalar::I32);
    let fill = Expr::Fill(b(Expr::Lit(3, Ty::U64)), b(Expr::Lit(0, Ty::I32)));
    let body = List::Cons(
        Box::new(Stmt::Local(X, vec, fill, 21)),
        Box::new(List::Cons(Box::new(Stmt::Local(A, vec, Expr::Move(X, vec), 22)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 23))))),
    );
    let f = Function { name: 453, line: 20, params: List::Nil, ret: Ty::I32, trusted: false, conds: List::Nil, body };
    let Model::Full(m) = translate_function(&f, &List::Nil, &List::Nil) else { panic!("a full model") };
    let List::Cons((first, _), rest) = strip(m.body) else { panic!("a body") };
    assert!(matches!(&*first, DStmt::Local(v, _, DExpr::SeqFill(..)) if *v == X), "{first:?}");
    let List::Cons((second, _), _) = *rest else { panic!("a move") };
    assert!(
        matches!(&*second, DStmt::Gone(inner, w, false) if *w == X && matches!(&**inner, DStmt::Local(v, _, DExpr::Var(src)) if *v == A && *src == X)),
        "{second:?}"
    );
}

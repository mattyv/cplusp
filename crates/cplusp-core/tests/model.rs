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
    let run = |t: u32, a: DArgs, rest: DCalls| List::Cons((t, DTy::Int32, SAT, a), Box::new(rest));
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
    let c = |l: u32| call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], l);
    let positive = |l: u32| Expr::Bin(BinOp::Gt, b(c(l)), b(Expr::Lit(0, Ty::I32)));
    let with = |s: Stmt| Function { body: List::Cons(Box::new(s), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 50)))), ..succ(Expr::Lit(0, Ty::I32)) };
    // if (true && sat(1, 2) > 0) {}: the right of && may not run.
    let and = Expr::Bin(BinOp::And, b(Expr::Bool(true)), b(positive(42)));
    let f = with(Stmt::If(and, Box::new(List::Nil), Box::new(List::Nil), 42));
    assert_eq!(bare_refusal(translate_function(&f, &all, &List::Nil)), Refusal::Place(42));
    // return true ? sat(1, 2) : 0; a branch may not run.
    let branch = Expr::Cond(b(Expr::Bool(true)), b(c(44)), b(Expr::Lit(0, Ty::I32)));
    assert_eq!(bare_refusal(translate_function(&succ(branch), &all, &List::Nil)), Refusal::Place(44));
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

#[test]
fn a_struct_that_holds_a_sequence_is_refused_as_a_local_or_a_result() {
    let param = |t: Ty| List::Cons((A, t), Box::new(List::Nil));
    // A local of Node, and a local of Wrapper, which holds a Node by value.
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
        assert_eq!(bare_refusal(translate_function(&f, &List::Nil, &node_table())), Refusal::HoldsSeq(15));
    }
    // A result of Node: the function has no method, so a call to it is refused at the call.
    let result = Function { name: SUCC, line: 19, params: param(Ty::Struct(NODE)), ret: Ty::Struct(NODE), trusted: false, conds: List::Nil, body: one(Stmt::Return(read(A, Ty::Struct(NODE)), 20)) };
    let caller = Function {
        name: SAT,
        line: 23,
        params: param(Ty::Struct(NODE)),
        ret: Ty::I32,
        trusted: false, conds: List::Nil,
        body: List::Cons(
            Box::new(Stmt::Local(B, Ty::I32, Expr::Call(SUCC, SAT_NAME, Box::new(List::Cons(b(read(A, Ty::Struct(NODE))), Box::new(List::Nil))), 24), 24)),
            Box::new(List::Cons(Box::new(Stmt::Return(Expr::Lit(0, Ty::I32), 25)), Box::new(List::Nil)))),
    };
    let all = fns(vec![result, caller]);
    let List::Cons(first, rest) = translate_unit(&all, &node_table()) else { panic!("two models") };
    assert_eq!(first, Model::Refused(Refusal::HoldsSeq(19)));
    let List::Cons(second, _) = *rest else { panic!("two models") };
    assert_eq!(bare_refusal(second), Refusal::Callee(SAT_NAME, 24));
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
fn a_member_function_with_a_local_or_a_call_is_not_pure_and_a_free_function_never_is() {
    let field = || Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let body = List::Cons(Box::new(Stmt::Local(A, Ty::I32, field(), 10)), Box::new(one(Stmt::Return(read(A, Ty::I32), 11))));
    let Model::Full(m) = translate_function(&value_fn(body), &List::Nil, &members_table(None, None)) else { panic!("a full model") };
    assert_eq!(m.function, None);
    assert_eq!(m.ensures, List::Nil);
    let free = Function { name: SAT, line: 3, params: List::Cons((X, Ty::I32), Box::new(List::Nil)), ret: Ty::I32, trusted: false, conds: List::Nil, body: one(Stmt::Return(read(X, Ty::I32), 4)) };
    let Model::Full(m) = translate_function(&free, &List::Nil, &List::Nil) else { panic!("a full model") };
    assert_eq!(m.function, None);
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
    // The table claims that value is pure and valid is not. The unit computes it: value is pure, and valid, here a member with a
    // local, is not. So a contract that calls valid() is refused, and one that calls c.value() reads the function.
    let field = || Expr::Cast(CastKind::Read, b(Expr::Field(b(Expr::Var(THIS, Ty::This(COUNTER))), CN)));
    let value = value_fn(one(Stmt::Return(field(), 10)));
    let valid = Function {
        name: VKEY,
        line: 12,
        params: List::Cons((THIS, Ty::This(COUNTER)), Box::new(List::Nil)),
        ret: Ty::Bool,
        trusted: false, conds: List::Nil,
        body: List::Cons(Box::new(Stmt::Local(B, Ty::Bool, Expr::Bool(true), 13)), Box::new(one(Stmt::Return(read(B, Ty::Bool), 14)))),
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

#[test]
fn a_constructor_of_a_struct_that_holds_a_sequence_is_refused() {
    let f = Function {
        name: CTOR,
        line: 9,
        params: List::Nil,
        ret: Ty::This(NODE),
        trusted: false, conds: List::Nil,
        body: one(Stmt::Return(Expr::Lit(0, Ty::I32), 9)),
    };
    assert_eq!(translate_function(&f, &List::Nil, &node_table()), Model::Refused(Refusal::HoldsSeq(9)));
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
    // The call writes x, so it has no place inside an expression: return next(x) + 1;
    let inside = Expr::Bin(BinOp::Add, b(call(NEXT, vec![Expr::Var(X, mut32())], 43)), b(Expr::Lit(1, Ty::I32)));
    let g = Function { body: one(Stmt::Return(inside, 43)), ..user };
    assert_eq!(bare_refusal(translate_function(&g, &all, &List::Nil)), Refusal::Place(43));
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

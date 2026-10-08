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

fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}

fn var(n: u32) -> Expr {
    Expr::Var(n, Ty::I32)
}

fn params() -> Params {
    Params::Cons(X, Ty::I32, Box::new(Params::Cons(LO, Ty::I32, Box::new(Params::Cons(HI, Ty::I32, Box::new(Params::Nil))))))
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
fn clamp_translates_to_a_method_whose_contract_reads_exact_integers() {
    // requires lo <= hi; ensures x < lo ==> result == lo; if (x < lo) { return lo; } return x;
    let conds = Conds::Cons(
        CondKind::Requires,
        Expr::Bin(BinOp::Le, b(Expr::Name(LO)), b(Expr::Name(HI))),
        21,
        Box::new(Conds::Cons(
            CondKind::Ensures,
            Expr::Bin(BinOp::Implies, b(Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Name(LO)))), b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(LO))))),
            22,
            Box::new(Conds::Nil),
        )),
    );
    let body = Stmts::Cons(
        Box::new(Stmt::If(
            Expr::Bin(BinOp::Lt, b(var(X)), b(var(LO))),
            Box::new(Stmts::Cons(Box::new(Stmt::Return(var(LO), 28)), Box::new(Stmts::Nil))),
            Box::new(Stmts::Nil),
            27,
        )),
        Box::new(Stmts::Cons(Box::new(Stmt::Return(var(X), 30)), Box::new(Stmts::Nil))),
    );
    let f = Function { name: CLAMP, line: 26, params: params(), ret: Ty::I32, conds, body };
    let Model::Full(m) = translate_function(&f, &Fns::Nil) else { panic!("clamp has a full model") };
    let as_int = |n: u32| DExpr::AsInt(Box::new(DExpr::Var(n)));
    assert_eq!(m.requires, DConds::Cons(DExpr::Bin(BinOp::Le, Box::new(as_int(LO)), Box::new(as_int(HI))), Box::new(DConds::Nil)));
    assert_eq!(
        m.ensures,
        DConds::Cons(
            DExpr::Bin(
                BinOp::Implies,
                Box::new(DExpr::Bin(BinOp::Lt, Box::new(as_int(X)), Box::new(as_int(LO)))),
                Box::new(DExpr::Bin(BinOp::Eq, Box::new(DExpr::AsInt(Box::new(DExpr::Result))), Box::new(as_int(LO))))
            ),
            Box::new(DConds::Nil)
        )
    );
    // The body keeps the machine operators: no `as int` in code.
    assert_eq!(
        m.body,
        DStmts::Cons(
            Box::new(DStmt::If(
                DExpr::Bin(BinOp::Lt, Box::new(DExpr::Var(X)), Box::new(DExpr::Var(LO))),
                Box::new(DStmts::Cons(Box::new(DStmt::Return(DExpr::Var(LO))), Box::new(DStmts::Nil))),
                Box::new(DStmts::Nil)
            )),
            Box::new(DStmts::Cons(Box::new(DStmt::Return(DExpr::Var(X))), Box::new(DStmts::Nil)))
        )
    );
    assert_eq!(m.ret, DTy::Int32);
}

fn one(s: Stmt) -> Stmts {
    Stmts::Cons(Box::new(s), Box::new(Stmts::Nil))
}

fn fns(v: Vec<Function>) -> Fns {
    v.into_iter().rev().fold(Fns::Nil, |rest, f| Fns::Cons(Box::new(f), Box::new(rest)))
}

fn read(n: u32, t: Ty) -> Expr {
    Expr::Cast(CastKind::Read, b(Expr::Var(n, t)))
}

/// `int32_t saturating_add(int32_t a, int32_t b)`, with a body of `body`.
fn sat(body: Stmts) -> Function {
    let ps = Params::Cons(A, Ty::I32, Box::new(Params::Cons(B, Ty::I32, Box::new(Params::Nil))));
    Function { name: SAT, line: 10, params: ps, ret: Ty::I32, conds: Conds::Nil, body }
}

/// `int32_t successor(int32_t x) { return <e>; }`
fn succ(e: Expr) -> Function {
    Function { name: SUCC, line: 37, params: Params::Cons(X, Ty::I32, Box::new(Params::Nil)), ret: Ty::I32, conds: Conds::Nil, body: one(Stmt::Return(e, 38)) }
}

fn call(key: u32, args: Vec<Expr>, line: u32) -> Expr {
    let args = args.into_iter().rev().fold(Args::Nil, |rest, e| Args::Cons(Box::new(e), Box::new(rest)));
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
    let body = Stmts::Cons(Box::new(Stmt::Local(SUM, Ty::I64, sum, 11)), Box::new(one(Stmt::Return(back, 18))));
    let Model::Full(m) = translate_function(&sat(body), &Fns::Nil) else { panic!("saturating_add has a full model") };
    let conv = |t: DTy, d: DExpr| DExpr::Conv(t, Box::new(d));
    let dsum = DExpr::Bin(BinOp::Add, Box::new(conv(DTy::Int64, DExpr::Var(A))), Box::new(conv(DTy::Int64, DExpr::Var(B))));
    assert_eq!(
        m.body,
        DStmts::Cons(
            Box::new(DStmt::Local(SUM, DTy::Int64, dsum)),
            Box::new(DStmts::Cons(Box::new(DStmt::Return(conv(DTy::Int32, DExpr::Var(SUM)))), Box::new(DStmts::Nil)))
        )
    );
}

#[test]
fn a_call_that_stands_alone_names_the_method_of_its_callee() {
    // successor: return saturating_add(x, 1); and a local whose start value is the call.
    let all = fns(vec![sat(one(Stmt::Return(Expr::Int(0), 15))), succ(call(SAT, vec![read(X, Ty::I32), Expr::Int(1)], 38))]);
    let Models::Cons(_, rest) = translate_unit(&all) else { panic!("two models") };
    let Models::Cons(Model::Full(m), _) = *rest else { panic!("successor has a full model") };
    let args = DArgs::Cons(DExpr::Var(X), Box::new(DArgs::Cons(DExpr::Lit(1), Box::new(DArgs::Nil))));
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::ReturnCall(SAT, args)), Box::new(DStmts::Nil)));

    let local = Stmt::Local(A, Ty::I32, call(SAT, vec![Expr::Int(1), Expr::Int(2)], 39), 39);
    let f = Function { body: Stmts::Cons(Box::new(local), Box::new(one(Stmt::Return(read(A, Ty::I32), 40)))), ..succ(Expr::Int(0)) };
    let Model::Full(m) = translate_function(&f, &all) else { panic!("a local from a call has a full model") };
    let DStmts::Cons(first, _) = m.body else { panic!("a body") };
    let args = DArgs::Cons(DExpr::Lit(1), Box::new(DArgs::Cons(DExpr::Lit(2), Box::new(DArgs::Nil))));
    assert_eq!(*first, DStmt::LocalCall(A, DTy::Int32, SAT, args));
}

#[test]
fn a_call_inside_an_expression_or_an_argument_is_refused_at_its_line() {
    let all = fns(vec![sat(one(Stmt::Return(Expr::Int(0), 15)))]);
    let plus = Expr::Bin(BinOp::Add, b(call(SAT, vec![Expr::Int(1), Expr::Int(2)], 38)), b(Expr::Int(1)));
    assert_eq!(bare_refusal(translate_function(&succ(plus), &all)), Refusal::Place(38));
    let nested = call(SAT, vec![call(SAT, vec![Expr::Int(1), Expr::Int(2)], 39), Expr::Int(2)], 39);
    assert_eq!(bare_refusal(translate_function(&succ(nested), &all)), Refusal::Place(39));
    let cond = Stmt::If(call(SAT, vec![Expr::Int(1), Expr::Int(2)], 40), Box::new(Stmts::Nil), Box::new(Stmts::Nil), 40);
    let f = Function { body: one(cond), ..succ(Expr::Int(0)) };
    assert_eq!(bare_refusal(translate_function(&f, &all)), Refusal::Place(40));
}

#[test]
fn a_call_to_a_function_with_no_method_is_refused_by_the_callee_name() {
    let to_sat = succ(call(SAT, vec![Expr::Int(1), Expr::Int(2)], 38));
    // No such function in the unit.
    assert_eq!(bare_refusal(translate_function(&to_sat, &Fns::Nil)), Refusal::Callee(SAT_NAME, 38));
    // The callee is in the unit, but its signature is not in the subset, so it has no method.
    let odd = Function { ret: Ty::Other(OTHER_TYPE), ..sat(Stmts::Nil) };
    let all = fns(vec![odd, to_sat]);
    let Models::Cons(first, rest) = translate_unit(&all) else { panic!("two models") };
    assert_eq!(first, Model::Refused(Refusal::Construct(OTHER_TYPE, 10)));
    let Models::Cons(second, _) = *rest else { panic!("two models") };
    assert_eq!(bare_refusal(second), Refusal::Callee(SAT_NAME, 38));
}

#[test]
fn a_callee_whose_body_is_refused_keeps_a_method_with_no_contract() {
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))), 9, Box::new(Conds::Nil));
    let refused = Function { conds, ..sat(one(Stmt::Return(Expr::Unknown(CALL_EXPR, 11), 11))) };
    let all = fns(vec![refused, succ(call(SAT, vec![Expr::Int(1), Expr::Int(2)], 38))]);
    let Models::Cons(first, rest) = translate_unit(&all) else { panic!("two models") };
    let Model::Bare(name, params, ret, r) = first else { panic!("a bare model: {first:?}") };
    assert_eq!((name, ret, r), (SAT, DTy::Int32, Refusal::Construct(CALL_EXPR, 11)));
    assert_eq!(params, DParams::Cons(A, DTy::Int32, Box::new(DParams::Cons(B, DTy::Int32, Box::new(DParams::Nil)))));
    let Models::Cons(Model::Full(_), _) = *rest else { panic!("the caller has a full model") };
}

#[test]
fn a_contract_line_the_shell_could_not_read_keeps_the_signature() {
    let conds = Conds::Cons(CondKind::Bad(Refusal::Syntax(9)), Expr::Int(0), 9, Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Int(0), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Syntax(9));
    let conds = Conds::Cons(CondKind::Bad(Refusal::Backslash(8)), Expr::Int(0), 8, Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Int(0), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Backslash(8));
}

#[test]
fn each_name_is_declared_once_in_a_function() {
    // int32_t a = 1; in a function with a parameter a.
    let f = sat(Stmts::Cons(Box::new(Stmt::Local(A, Ty::I32, Expr::Int(1), 12)), Box::new(one(Stmt::Return(Expr::Int(0), 15)))));
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Twice(A, 12));
    // int32_t sum = 1; if (..) { int32_t sum = 2; }
    let inner = Stmt::If(Expr::Bin(BinOp::Lt, b(read(A, Ty::I32)), b(Expr::Int(0))), Box::new(one(Stmt::Local(SUM, Ty::I64, Expr::Int(2), 14))), Box::new(Stmts::Nil), 14);
    let body = Stmts::Cons(Box::new(Stmt::Local(SUM, Ty::I64, Expr::Int(1), 13)), Box::new(Stmts::Cons(Box::new(inner), Box::new(one(Stmt::Return(Expr::Int(0), 15))))));
    assert_eq!(bare_refusal(translate_function(&sat(body), &Fns::Nil)), Refusal::Twice(SUM, 14));
}

#[test]
fn a_conversion_between_bool_and_a_number_is_refused() {
    let to_bool = Expr::Cast(CastKind::Integral(Ty::Bool, Ty::I32), b(Expr::Var(A, Ty::Bool)));
    // A refusal inside an expression is at the line of its statement.
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(to_bool, 12))), &Fns::Nil)), Refusal::Convert(12));
    // A type with no rule inside a cast is refused by that type, before the bool rule.
    let odd = Expr::Cast(CastKind::Integral(Ty::Other(OTHER_TYPE), Ty::I32), b(Expr::Var(A, Ty::I32)));
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(odd, 13))), &Fns::Nil)), Refusal::Construct(OTHER_TYPE, 13));
}

#[test]
fn a_node_with_no_rule_is_refused_with_its_kind_and_line() {
    let body = Stmts::Cons(Box::new(Stmt::Return(Expr::Unknown(CALL_EXPR, 38), 38)), Box::new(Stmts::Nil));
    let f = Function { name: CLAMP, line: 37, params: params(), ret: Ty::I32, conds: Conds::Nil, body };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Construct(CALL_EXPR, 38));
}

#[test]
fn a_contract_name_that_is_no_parameter_is_refused() {
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(99))), 5, Box::new(Conds::Nil));
    let f = Function { name: CLAMP, line: 6, params: params(), ret: Ty::I32, conds, body: Stmts::Nil };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Name(99, 5));
}

#[test]
fn a_signature_outside_the_subset_has_no_method() {
    let f = Function { ret: Ty::Other(OTHER_TYPE), ..sat(Stmts::Nil) };
    assert_eq!(translate_function(&f, &Fns::Nil), Model::Refused(Refusal::Construct(OTHER_TYPE, 10)));
}

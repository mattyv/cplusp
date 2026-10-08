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
    v.iter().rev().fold(Names::Nil, |rest, n| Names::Cons(*n, Box::new(rest)))
}

/// A literal of code prints with its type, decision 0061.
fn lit32(n: u64) -> DExpr {
    DExpr::Conv(DTy::Int32, Box::new(DExpr::Lit(n)))
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
    let conds = Conds::Cons(
        CondKind::Requires,
        Expr::Bin(BinOp::Le, b(Expr::Name(LO)), b(Expr::Name(HI))),
        21,
        names(&[X, LO, HI]),
        Box::new(Conds::Cons(
            CondKind::Ensures,
            Expr::Bin(BinOp::Implies, b(Expr::Bin(BinOp::Lt, b(Expr::Name(X)), b(Expr::Name(LO)))), b(Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(LO))))),
            22,
            names(&[X, LO, HI]),
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
    let all = fns(vec![sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))), succ(call(SAT, vec![read(X, Ty::I32), Expr::Lit(1, Ty::I32)], 38))]);
    let Models::Cons(_, rest) = translate_unit(&all) else { panic!("two models") };
    let Models::Cons(Model::Full(m), _) = *rest else { panic!("successor has a full model") };
    let args = DArgs::Cons(DExpr::Var(X), Box::new(DArgs::Cons(lit32(1), Box::new(DArgs::Nil))));
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::ReturnCall(SAT, args)), Box::new(DStmts::Nil)));

    let local = Stmt::Local(A, Ty::I32, call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 39), 39);
    let f = Function { body: Stmts::Cons(Box::new(local), Box::new(one(Stmt::Return(read(A, Ty::I32), 40)))), ..succ(Expr::Lit(0, Ty::I32)) };
    let Model::Full(m) = translate_function(&f, &all) else { panic!("a local from a call has a full model") };
    let DStmts::Cons(first, _) = m.body else { panic!("a body") };
    let args = DArgs::Cons(lit32(1), Box::new(DArgs::Cons(lit32(2), Box::new(DArgs::Nil))));
    assert_eq!(*first, DStmt::LocalCall(A, DTy::Int32, SAT, args));
}

#[test]
fn a_call_inside_an_expression_or_an_argument_is_refused_at_its_line() {
    let all = fns(vec![sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)))]);
    let plus = Expr::Bin(BinOp::Add, b(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 38)), b(Expr::Lit(1, Ty::I32)));
    assert_eq!(bare_refusal(translate_function(&succ(plus), &all)), Refusal::Place(38));
    let nested = call(SAT, vec![call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 39), Expr::Lit(2, Ty::I32)], 39);
    assert_eq!(bare_refusal(translate_function(&succ(nested), &all)), Refusal::Place(39));
    let cond = Stmt::If(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 40), Box::new(Stmts::Nil), Box::new(Stmts::Nil), 40);
    let f = Function { body: one(cond), ..succ(Expr::Lit(0, Ty::I32)) };
    assert_eq!(bare_refusal(translate_function(&f, &all)), Refusal::Place(40));
}

#[test]
fn a_call_to_a_function_with_no_method_is_refused_by_the_callee_name() {
    let to_sat = succ(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 38));
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
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))), 9, names(&[A, B]), Box::new(Conds::Nil));
    let refused = Function { conds, ..sat(one(Stmt::Return(Expr::Unknown(CALL_EXPR, 11), 11))) };
    let all = fns(vec![refused, succ(call(SAT, vec![Expr::Lit(1, Ty::I32), Expr::Lit(2, Ty::I32)], 38))]);
    let Models::Cons(first, rest) = translate_unit(&all) else { panic!("two models") };
    let Model::Bare(name, params, ret, r) = first else { panic!("a bare model: {first:?}") };
    assert_eq!((name, ret, r), (SAT, DTy::Int32, Refusal::Construct(CALL_EXPR, 11)));
    assert_eq!(params, DParams::Cons(A, DTy::Int32, Box::new(DParams::Cons(B, DTy::Int32, Box::new(DParams::Nil)))));
    let Models::Cons(Model::Full(_), _) = *rest else { panic!("the caller has a full model") };
}

#[test]
fn a_contract_line_the_shell_could_not_read_keeps_the_signature() {
    let conds = Conds::Cons(CondKind::Bad(Refusal::Syntax(9)), Expr::Int(0), 9, Names::Nil, Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Syntax(9));
    let conds = Conds::Cons(CondKind::Bad(Refusal::Backslash(8)), Expr::Int(0), 8, Names::Nil, Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Backslash(8));
}

#[test]
fn each_name_is_declared_once_in_a_function() {
    // int32_t a = 1; in a function with a parameter a.
    let f = sat(Stmts::Cons(Box::new(Stmt::Local(A, Ty::I32, Expr::Lit(1, Ty::I32), 12)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15)))));
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Twice(A, 12));
    // int32_t sum = 1; if (..) { int32_t sum = 2; }
    let inner = Stmt::If(Expr::Bin(BinOp::Lt, b(read(A, Ty::I32)), b(Expr::Lit(0, Ty::I32))), Box::new(one(Stmt::Local(SUM, Ty::I64, Expr::Lit(2, Ty::I32), 14))), Box::new(Stmts::Nil), 14);
    let body = Stmts::Cons(Box::new(Stmt::Local(SUM, Ty::I64, Expr::Lit(1, Ty::I32), 13)), Box::new(Stmts::Cons(Box::new(inner), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))))));
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
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(99))), 5, names(&[X, LO, HI]), Box::new(Conds::Nil));
    let f = Function { name: CLAMP, line: 6, params: params(), ret: Ty::I32, conds, body: Stmts::Nil };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Name(99, 5));
}

#[test]
fn a_signature_outside_the_subset_has_no_method() {
    let f = Function { ret: Ty::Other(OTHER_TYPE), ..sat(Stmts::Nil) };
    assert_eq!(translate_function(&f, &Fns::Nil), Model::Refused(Refusal::Construct(OTHER_TYPE, 10)));
}

#[test]
fn a_literal_of_a_type_outside_the_subset_is_refused() {
    // return -1u < 1u; C++ wraps the negation, so a literal that lost its type would give the wrong result.
    let unsigned = |n: u64| Expr::Lit(n, Ty::Other(OTHER_TYPE));
    let e = Expr::Bin(BinOp::Lt, b(Expr::Neg(b(unsigned(1)))), b(unsigned(1)));
    assert_eq!(bare_refusal(translate_function(&sat(one(Stmt::Return(e, 6))), &Fns::Nil)), Refusal::Construct(OTHER_TYPE, 6));
}

#[test]
fn a_contract_reads_the_parameters_of_its_declaration_by_place() {
    // int32_t sat(int32_t p, int32_t q) with ensures result == p - q, and the definition sat(int32_t a, int32_t b).
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Sub, b(Expr::Name(P)), b(Expr::Name(Q)))));
    let conds = Conds::Cons(CondKind::Ensures, ens, 9, names(&[P, Q]), Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    let Model::Full(m) = translate_function(&f, &Fns::Nil) else { panic!("a full model") };
    let as_int = |d: DExpr| Box::new(DExpr::AsInt(Box::new(d)));
    let want = DExpr::Bin(BinOp::Eq, as_int(DExpr::Result), Box::new(DExpr::Bin(BinOp::Sub, as_int(DExpr::Var(A)), as_int(DExpr::Var(B)))));
    assert_eq!(m.ensures, DConds::Cons(want, Box::new(DConds::Nil)));
    // The declaration says (b, a). Its `a` is the definition's second parameter, `b`, and its `b` is the first, `a`.
    let ens = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Bin(BinOp::Sub, b(Expr::Name(A)), b(Expr::Name(B)))));
    let conds = Conds::Cons(CondKind::Ensures, ens, 9, names(&[B, A]), Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    let Model::Full(m) = translate_function(&f, &Fns::Nil) else { panic!("a full model") };
    let want = DExpr::Bin(BinOp::Eq, as_int(DExpr::Result), Box::new(DExpr::Bin(BinOp::Sub, as_int(DExpr::Var(B)), as_int(DExpr::Var(A)))));
    assert_eq!(m.ensures, DConds::Cons(want, Box::new(DConds::Nil)));
    // A name of the definition that the declaration does not have is no parameter of the contract.
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(A))), 9, names(&[P, Q]), Box::new(Conds::Nil));
    let f = Function { conds, ..sat(one(Stmt::Return(Expr::Lit(0, Ty::I32), 15))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Name(A, 9));
}

/// `int32_t n` alone, with a body.
fn with_n(body: Stmts) -> Function {
    Function { name: SAT, line: 3, params: Params::Cons(X, Ty::I32, Box::new(Params::Nil)), ret: Ty::I32, conds: Conds::Nil, body }
}

fn conds(v: Vec<(CondKind, Expr, u32)>) -> Conds {
    v.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l)| Conds::Cons(k, e, l, Names::Nil, Box::new(rest)))
}

#[test]
fn a_literal_of_code_carries_its_type_into_dafny() {
    let m = translate_function(&with_n(one(Stmt::Return(Expr::Lit(7, Ty::I32), 4))), &Fns::Nil);
    let Model::Full(m) = m else { panic!("a full model") };
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::Return(lit32(7))), Box::new(DStmts::Nil)));
    // The unsigned types of decision 0061.
    let m = translate_function(&with_n(one(Stmt::Return(Expr::Lit(7, Ty::U64), 4))), &Fns::Nil);
    let Model::Full(m) = m else { panic!("a full model") };
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::Return(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(7))))), Box::new(DStmts::Nil)));
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
    let body = Stmts::Cons(
        Box::new(Stmt::Local(acc, Ty::I32, Expr::Lit(0, Ty::I32), 4)),
        Box::new(Stmts::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(acc, Ty::I32), 10))))),
    );
    let Model::Full(m) = translate_function(&with_n(body), &Fns::Nil) else { panic!("a full model") };
    let DStmts::Cons(_, rest) = m.body else { panic!("a body") };
    let DStmts::Cons(lp, _) = *rest else { panic!("a loop") };
    let as_int = |n: u32| Box::new(DExpr::AsInt(Box::new(DExpr::Var(n))));
    let want = DStmt::For(
        Box::new(DStmt::Local(i, DTy::Int32, lit32(0))),
        DExpr::Bin(BinOp::Lt, Box::new(DExpr::Var(i)), Box::new(DExpr::Var(X))),
        DConds::Cons(DExpr::Bin(BinOp::Le, as_int(i), as_int(X)), Box::new(DConds::Nil)),
        DConds::Cons(DExpr::Bin(BinOp::Sub, as_int(X), as_int(i)), Box::new(DConds::Nil)),
        Box::new(DStmts::Cons(Box::new(DStmt::Assign(acc, DExpr::Bin(BinOp::Add, Box::new(DExpr::Var(acc)), Box::new(lit32(1))))), Box::new(DStmts::Nil))),
        Box::new(DStmt::Assign(i, DExpr::Bin(BinOp::Add, Box::new(DExpr::Var(i)), Box::new(lit32(1))))),
    );
    assert_eq!(*lp, want);
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
    let body = Stmts::Cons(Box::new(Stmt::Local(k, Ty::I32, read(X, Ty::I32), 4)), Box::new(Stmts::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(k, Ty::I32), 10))))));
    let Model::Full(m) = translate_function(&with_n(body), &Fns::Nil) else { panic!("a full model") };
    let DStmts::Cons(_, rest) = m.body else { panic!("a body") };
    let DStmts::Cons(lp, _) = *rest else { panic!("a loop") };
    let kk = || Box::new(DExpr::AsInt(Box::new(DExpr::Var(k))));
    let want = DStmt::While(
        DExpr::Bin(BinOp::Gt, Box::new(DExpr::Var(k)), Box::new(lit32(0))),
        DConds::Cons(DExpr::Bin(BinOp::Le, Box::new(DExpr::Lit(0)), kk()), Box::new(DConds::Nil)),
        DConds::Cons(*kk(), Box::new(DConds::Nil)),
        Box::new(DStmts::Cons(Box::new(DStmt::Assign(k, DExpr::Bin(BinOp::Sub, Box::new(DExpr::Var(k)), Box::new(lit32(1))))), Box::new(DStmts::Nil))),
    );
    assert_eq!(*lp, want);
}

#[test]
fn a_write_to_a_parameter_is_refused() {
    let body = Stmts::Cons(Box::new(Stmt::Assign(X, Expr::Lit(1, Ty::I32), 5)), Box::new(one(Stmt::Return(read(X, Ty::I32), 6))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &Fns::Nil)), Refusal::WriteParam(X, 5));
    let body = Stmts::Cons(Box::new(Stmt::Step(X, Ty::I32, true, 5)), Box::new(one(Stmt::Return(read(X, Ty::I32), 6))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &Fns::Nil)), Refusal::WriteParam(X, 5));
}

#[test]
fn a_loop_contract_names_only_variables_and_never_result() {
    let lp = |lc: Conds| Stmt::While(Expr::Lit(1, Ty::Bool), Box::new(lc), Box::new(Stmts::Nil), 7);
    let f = |lc: Conds| with_n(Stmts::Cons(Box::new(lp(lc)), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 9)))));
    let unbound = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Le, b(Expr::Name(X)), b(Expr::Name(99))), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(unbound), &Fns::Nil)), Refusal::NoVar(99, 6));
    let result = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Int(0))), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(result), &Fns::Nil)), Refusal::Syntax(6));
    let ensures = conds(vec![(CondKind::Ensures, Expr::Name(X), 6)]);
    assert_eq!(bare_refusal(translate_function(&f(ensures), &Fns::Nil)), Refusal::Misplaced(6));
}

#[test]
fn a_loop_contract_line_above_a_function_is_refused() {
    let fc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Lt, b(Expr::Int(0)), b(Expr::Name(X))), 2)]);
    let f = Function { conds: fc, ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Misplaced(2));
}

#[test]
fn a_name_declared_in_a_loop_counts_for_declared_once() {
    // int32_t i = 0; for (int32_t i = 0; ...) — the start of the for declares i a second time.
    let start = Stmt::Local(SUM, Ty::I32, Expr::Lit(0, Ty::I32), 6);
    let lp = Stmt::For(Box::new(start), Expr::Lit(0, Ty::Bool), Box::new(Stmt::Step(SUM, Ty::I32, true, 6)), Box::new(Conds::Nil), Box::new(Stmts::Nil), 6);
    let body = Stmts::Cons(Box::new(Stmt::Local(SUM, Ty::I32, Expr::Lit(0, Ty::I32), 5)), Box::new(Stmts::Cons(Box::new(lp), Box::new(one(Stmt::Return(Expr::Lit(0, Ty::I32), 7))))));
    assert_eq!(bare_refusal(translate_function(&with_n(body), &Fns::Nil)), Refusal::Twice(SUM, 6));
}

#[test]
fn a_loop_contract_reads_only_the_variables_in_scope_at_the_loop() {
    // int32_t i = 0; invariant t == 1; while (...) { int32_t t = 1; ++i; }
    let (i, t) = (SUM, A);
    let lc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Name(t)), b(Expr::Int(1))), 5)]);
    let body = Stmts::Cons(Box::new(Stmt::Local(t, Ty::I32, Expr::Lit(1, Ty::I32), 7)), Box::new(one(Stmt::Step(i, Ty::I32, true, 8))));
    let lp = Stmt::While(Expr::Bin(BinOp::Lt, b(read(i, Ty::I32)), b(read(X, Ty::I32))), Box::new(lc), Box::new(body), 6);
    let f = with_n(Stmts::Cons(Box::new(Stmt::Local(i, Ty::I32, Expr::Lit(0, Ty::I32), 4)), Box::new(Stmts::Cons(Box::new(lp), Box::new(one(Stmt::Return(read(i, Ty::I32), 10)))))));
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::NoVar(t, 5));
    // A local declared after the loop.
    let lc = conds(vec![(CondKind::Invariant, Expr::Bin(BinOp::Eq, b(Expr::Name(t)), b(Expr::Int(1))), 5)]);
    let lp = Stmt::While(Expr::Bin(BinOp::Lt, b(read(i, Ty::I32)), b(read(X, Ty::I32))), Box::new(lc), Box::new(one(Stmt::Step(i, Ty::I32, true, 7))), 6);
    let tail = Stmts::Cons(Box::new(Stmt::Local(t, Ty::I32, Expr::Lit(1, Ty::I32), 9)), Box::new(one(Stmt::Return(read(t, Ty::I32), 10))));
    let f = with_n(Stmts::Cons(Box::new(Stmt::Local(i, Ty::I32, Expr::Lit(0, Ty::I32), 4)), Box::new(Stmts::Cons(Box::new(lp), Box::new(tail)))));
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::NoVar(t, 5));
}

#[test]
fn bool_literals_and_the_largest_uint64_literal_translate() {
    let f = |e: Expr, ret: Ty| Function { ret, ..with_n(one(Stmt::Return(e, 4))) };
    let Model::Full(m) = translate_function(&f(Expr::Bool(true), Ty::Bool), &Fns::Nil) else { panic!("a full model") };
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::Return(DExpr::Bool(true))), Box::new(DStmts::Nil)));
    let Model::Full(m) = translate_function(&f(Expr::Lit(u64::MAX, Ty::U64), Ty::U64), &Fns::Nil) else { panic!("a full model") };
    let want = DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(u64::MAX)));
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::Return(want)), Box::new(DStmts::Nil)));
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
    let conds = Conds::Cons(CondKind::Ensures, Expr::Forall(j, b(body)), 3, names(&[v]), Box::new(Conds::Nil));
    let f = Function {
        name: SAT,
        line: 4,
        params: Params::Cons(v, Ty::Seq(Scalar::I32), Box::new(Params::Nil)),
        ret: Ty::Bool,
        conds,
        body: one(Stmt::Return(Expr::Bool(true), 5)),
    };
    let Model::Full(m) = translate_function(&f, &Fns::Nil) else { panic!("a full model") };
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
    assert_eq!(m.ensures, DConds::Cons(want, Box::new(DConds::Nil)));
    // The method requires that the length of the sequence fits size_t.
    let bound = DExpr::Bin(BinOp::Le, len(), Box::new(DExpr::Lit(u64::MAX)));
    assert_eq!(m.requires, DConds::Cons(bound, Box::new(DConds::Nil)));
}

#[test]
fn code_reads_a_sequence_by_size_and_index() {
    // return v[0] < v.size(); with v of seq<uint8>: the size is (|v| as uint64).
    let v = X;
    let seq = Ty::Seq(Scalar::U8);
    let idx = Expr::Index(b(Expr::Var(v, seq)), b(Expr::Lit(0, Ty::U64)));
    let size = Expr::Size(b(Expr::Var(v, seq)));
    let e = Expr::Bin(BinOp::Lt, b(Expr::Cast(CastKind::Integral(Ty::U8, Ty::U64), b(Expr::Cast(CastKind::Read, b(idx))))), b(size));
    let f = Function { name: SAT, line: 4, params: Params::Cons(v, seq, Box::new(Params::Nil)), ret: Ty::Bool, conds: Conds::Nil, body: one(Stmt::Return(e, 5)) };
    let Model::Full(m) = translate_function(&f, &Fns::Nil) else { panic!("a full model") };
    let didx = DExpr::Index(Box::new(DExpr::Var(v)), Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0)))));
    let dsize = DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(DExpr::Var(v)))));
    let want = DExpr::Bin(BinOp::Lt, Box::new(DExpr::Conv(DTy::UInt64, Box::new(didx))), Box::new(dsize));
    assert_eq!(m.body, DStmts::Cons(Box::new(DStmt::Return(want)), Box::new(DStmts::Nil)));
}

#[test]
fn a_sequence_is_in_the_subset_only_as_a_parameter() {
    let seq = Ty::Seq(Scalar::I32);
    let f = Function { ret: seq, ..with_n(Stmts::Nil) };
    assert_eq!(translate_function(&f, &Fns::Nil), Model::Refused(Refusal::SeqParam(3)));
    let local = Stmt::Local(SUM, seq, Expr::Var(X, Ty::I32), 4);
    assert_eq!(bare_refusal(translate_function(&with_n(one(local)), &Fns::Nil)), Refusal::SeqParam(4));
}

#[test]
fn a_chain_of_two_directions_and_an_index_of_a_scalar_are_refused() {
    let ens = |e: Expr| Conds::Cons(CondKind::Ensures, e, 2, names(&[X]), Box::new(Conds::Nil));
    let mixed = Expr::Chain(BinOp::Lt, BinOp::Gt, b(Expr::Int(0)), b(Expr::Name(X)), b(Expr::Int(1)));
    let f = Function { conds: ens(mixed), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Syntax(2));
    let index = Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Index(b(Expr::Name(X)), b(Expr::Int(0)))));
    let f = Function { conds: ens(index), ..with_n(one(Stmt::Return(Expr::Lit(0, Ty::I32), 4))) };
    assert_eq!(bare_refusal(translate_function(&f, &Fns::Nil)), Refusal::Syntax(2));
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

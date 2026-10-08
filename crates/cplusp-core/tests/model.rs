//! The translator core on the shapes of `clamp`, decision 0056. The proofs in src/model.rs say that each function computes its
//! rule. These tests pin what the rules give for one real function, and for a refusal.

use cplusp_core::model::*;

const X: u32 = 1;
const LO: u32 = 2;
const HI: u32 = 3;
const CLAMP: u32 = 10;
const CALL_EXPR: u32 = 20;

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
            Box::new(Stmts::Cons(Box::new(Stmt::Return(var(LO))), Box::new(Stmts::Nil))),
            Box::new(Stmts::Nil),
        )),
        Box::new(Stmts::Cons(Box::new(Stmt::Return(var(X))), Box::new(Stmts::Nil))),
    );
    let f = Function { name: CLAMP, line: 26, params: params(), ret: Ty::I32, conds, body };
    let m = translate_function(&f).unwrap();
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

#[test]
fn a_node_with_no_rule_is_refused_with_its_kind_and_line() {
    let body = Stmts::Cons(Box::new(Stmt::Return(Expr::Unknown(CALL_EXPR, 38))), Box::new(Stmts::Nil));
    let f = Function { name: CLAMP, line: 37, params: params(), ret: Ty::I32, conds: Conds::Nil, body };
    assert_eq!(translate_function(&f), Err(Refusal::Construct(CALL_EXPR, 38)));
}

#[test]
fn a_contract_name_that_is_no_parameter_is_refused() {
    let conds = Conds::Cons(CondKind::Ensures, Expr::Bin(BinOp::Eq, b(Expr::Result), b(Expr::Name(99))), 5, Box::new(Conds::Nil));
    let f = Function { name: CLAMP, line: 6, params: params(), ret: Ty::I32, conds, body: Stmts::Nil };
    assert_eq!(translate_function(&f), Err(Refusal::Name(99, 5)));
}

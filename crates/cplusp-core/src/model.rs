//! The translator from the C++ subset to Dafny, decision 0056.
//!
//! The shell hands this module the compiler's tree of one function as plain data, and gets a Dafny method back or a refusal. Each
//! rule of the translation is a spec function here, and each exec function is proved to compute exactly its spec. The proofs say:
//!
//! - `translate_function`: the result is the spec model of the function, `spec_function`.
//! - a node that the translator does not know is refused, never skipped: `lemma_unknown_is_refused`.
//! - a translated body has one Dafny statement for each C++ statement: `lemma_statements_kept`.
//! - `parse_contract`: it ends, it reads every token or refuses the line, and an expression it gives holds no unknown node.
//!
//! The lists are cons lists, so that each rule and each proof is one structural recursion.
//! Names, kinds of construct and lines are numbers. The shell keeps the table of names and prints the text.

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ the C++ side

/// A type of the subset. `Other` is a type the translator has no rule for, by the id of its name.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Ty {
    I32,
    I64,
    U8,
    Bool,
    Other(u32),
}

/// A binary operator. In code it is the machine operator of its operand type. In a contract it is the operator on the exact
/// integers.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
    Implies,
}

/// An expression. In code, a name carries its type, which the compiler gave. In a contract, a name carries no type, and the
/// translator finds it among the parameters. `Unknown` is a construct with no rule, by the id of its kind and its line.
#[derive(PartialEq, Eq, Debug)]
pub enum Expr {
    Int(i64),
    Var(u32, Ty),
    Name(u32),
    Result,
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    Unknown(u32, u32),
}

/// A statement of the body.
#[derive(PartialEq, Eq, Debug)]
pub enum Stmt {
    Return(Expr),
    If(Expr, Box<Stmts>, Box<Stmts>),
    Unknown(u32, u32),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Stmts {
    Nil,
    Cons(Box<Stmt>, Box<Stmts>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Params {
    Nil,
    Cons(u32, Ty, Box<Params>),
}

/// What a contract line says. `Other` is a word the translator has no rule for yet, by the id of the word.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CondKind {
    Requires,
    Ensures,
    Other(u32),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Conds {
    Nil,
    Cons(CondKind, Expr, u32, Box<Conds>),
}

/// One function: its name, its parameters, its return type, its contract and its body. `line` is the line of its name.
#[derive(PartialEq, Eq, Debug)]
pub struct Function {
    pub name: u32,
    pub line: u32,
    pub params: Params,
    pub ret: Ty,
    pub conds: Conds,
    pub body: Stmts,
}

// ------------------------------------------------------------------ the Dafny side

#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum DTy {
    Int32,
    Int64,
    UInt8,
    Bool,
}

/// A Dafny expression. `AsInt` is `(e as int)`, the exact value of a machine integer.
#[derive(PartialEq, Eq, Debug)]
pub enum DExpr {
    Lit(i64),
    Var(u32),
    Result,
    Bin(BinOp, Box<DExpr>, Box<DExpr>),
    Not(Box<DExpr>),
    Neg(Box<DExpr>),
    AsInt(Box<DExpr>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DStmt {
    Return(DExpr),
    If(DExpr, Box<DStmts>, Box<DStmts>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DStmts {
    Nil,
    Cons(Box<DStmt>, Box<DStmts>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DParams {
    Nil,
    Cons(u32, DTy, Box<DParams>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DConds {
    Nil,
    Cons(DExpr, Box<DConds>),
}

/// A Dafny method.
#[derive(PartialEq, Eq, Debug)]
pub struct Method {
    pub name: u32,
    pub params: DParams,
    pub ret: DTy,
    pub requires: DConds,
    pub ensures: DConds,
    pub body: DStmts,
}

/// Why the translator refused. `Construct` is a node with no rule: the id of its kind and its line. `Name` is a name in a contract
/// that is no parameter. `Syntax` is a contract line the parser cannot read.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Refusal {
    Construct(u32, u32),
    Name(u32, u32),
    Syntax(u32),
}

// ------------------------------------------------------------------ the rules

/// A type of the subset maps to its Dafny newtype, decision 0029 and the battery case signed_overflow.
pub open spec fn spec_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::I32 => Ok(DTy::Int32),
        Ty::I64 => Ok(DTy::Int64),
        Ty::U8 => Ok(DTy::UInt8),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

/// An integer type, whose value a contract reads as an exact integer.
pub open spec fn is_integer(t: Ty) -> bool {
    t == Ty::I32 || t == Ty::I64 || t == Ty::U8
}

/// An expression of the body. The operators stay the machine operators of their newtype, so Dafny checks each step for
/// overflow, the battery case signed_overflow. A contract name or `result` has no place in code.
pub open spec fn spec_code(e: Expr, line: u32) -> Result<DExpr, Refusal>
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(n)),
        Expr::Var(v, t) => match spec_ty(t, line) {
            Ok(_) => Ok(DExpr::Var(v)),
            Err(r) => Err(r),
        },
        Expr::Bin(op, a, b) => match spec_code(*a, line) {
            Ok(da) => match spec_code(*b, line) {
                Ok(db) => Ok(DExpr::Bin(op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match spec_code(*a, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match spec_code(*a, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(n, line)),
        Expr::Result => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// The type of a parameter, if `name` is one.
pub open spec fn spec_lookup(ps: Params, name: u32) -> Option<Ty>
    decreases ps,
{
    match ps {
        Params::Nil => None,
        Params::Cons(n, t, rest) => if n == name {
            Some(t)
        } else {
            spec_lookup(*rest, name)
        },
    }
}

/// A leaf of a contract: an integer reads as its exact value, `(x as int)`, and a bool as itself.
pub open spec fn spec_leaf(d: DExpr, t: Ty, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(t, line) {
        Ok(_) => if is_integer(t) {
            Ok(DExpr::AsInt(Box::new(d)))
        } else {
            Ok(d)
        },
        Err(r) => Err(r),
    }
}

/// An expression of a contract. Arithmetic is on the exact integers, the battery case signed_overflow: each integer name and
/// `result` read as `as int`, so no step can overflow. A name must be a parameter.
pub open spec fn spec_contract(e: Expr, ps: Params, ret: Ty, line: u32) -> Result<DExpr, Refusal>
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(n)),
        Expr::Name(n) => match spec_lookup(ps, n) {
            Some(t) => spec_leaf(DExpr::Var(n), t, line),
            None => Err(Refusal::Name(n, line)),
        },
        Expr::Result => spec_leaf(DExpr::Result, ret, line),
        Expr::Bin(op, a, b) => match spec_contract(*a, ps, ret, line) {
            Ok(da) => match spec_contract(*b, ps, ret, line) {
                Ok(db) => Ok(DExpr::Bin(op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match spec_contract(*a, ps, ret, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match spec_contract(*a, ps, ret, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Var(v, _) => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// A statement of the body, and a list of them.
pub open spec fn spec_stmt(s: Stmt, line: u32) -> Result<DStmt, Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e) => match spec_code(e, line) {
            Ok(d) => Ok(DStmt::Return(d)),
            Err(r) => Err(r),
        },
        Stmt::If(c, t, f) => match spec_code(c, line) {
            Ok(dc) => match spec_stmts(*t, line) {
                Ok(dt) => match spec_stmts(*f, line) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

pub open spec fn spec_stmts(ss: Stmts, line: u32) -> Result<DStmts, Refusal>
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match spec_stmt(*s, line) {
            Ok(d) => match spec_stmts(*rest, line) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub open spec fn spec_params(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match spec_ty(t, line) {
            Ok(dt) => match spec_params(*rest, line) {
                Ok(dr) => Ok(DParams::Cons(n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The lines of one kind of the contract, in their order. A word with no rule is refused.
pub open spec fn spec_conds(cs: Conds, want: CondKind, ps: Params, ret: Ty) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            _ => match spec_conds(*rest, want, ps, ret) {
                Ok(dr) => if k == want {
                    match spec_contract(e, ps, ret, l) {
                        Ok(d) => Ok(DConds::Cons(d, Box::new(dr))),
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

/// The model of a function: a method with the same name, parameters, return type, contract and body.
pub open spec fn spec_function(f: Function) -> Result<Method, Refusal> {
    match spec_params(f.params, f.line) {
        Err(r) => Err(r),
        Ok(ps) => match spec_ty(f.ret, f.line) {
            Err(r) => Err(r),
            Ok(ret) => match spec_conds(f.conds, CondKind::Requires, f.params, f.ret) {
                Err(r) => Err(r),
                Ok(req) => match spec_conds(f.conds, CondKind::Ensures, f.params, f.ret) {
                    Err(r) => Err(r),
                    Ok(ens) => match spec_stmts(f.body, f.line) {
                        Err(r) => Err(r),
                        Ok(body) => Ok(Method { name: f.name, params: ps, ret, requires: req, ensures: ens, body }),
                    },
                },
            },
        },
    }
}

// ------------------------------------------------------------------ properties of the rules

pub open spec fn unknown_expr(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Unknown(_, _) => true,
        Expr::Bin(_, a, b) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Not(a) => unknown_expr(*a),
        Expr::Neg(a) => unknown_expr(*a),
        _ => false,
    }
}

pub open spec fn unknown_stmt(s: Stmt) -> bool
    decreases s,
{
    match s {
        Stmt::Unknown(_, _) => true,
        Stmt::Return(e) => unknown_expr(e),
        Stmt::If(c, t, f) => unknown_expr(c) || unknown_stmts(*t) || unknown_stmts(*f),
    }
}

pub open spec fn unknown_stmts(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        Stmts::Nil => false,
        Stmts::Cons(s, rest) => unknown_stmt(*s) || unknown_stmts(*rest),
    }
}

pub proof fn lemma_unknown_code_is_refused(e: Expr, line: u32)
    requires
        unknown_expr(e),
    ensures
        spec_code(e, line).is_err(),
    decreases e,
{
    match e {
        Expr::Bin(_, a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_code_is_refused(*a, line);
            } else {
                lemma_unknown_code_is_refused(*b, line);
            }
        },
        Expr::Not(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Neg(a) => lemma_unknown_code_is_refused(*a, line),
        _ => {},
    }
}

pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, line: u32)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, line).is_err(),
    decreases s,
{
    match s {
        Stmt::Return(e) => lemma_unknown_code_is_refused(e, line),
        Stmt::If(c, t, f) => {
            if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, line);
            } else if unknown_stmts(*t) {
                lemma_unknown_stmts_is_refused(*t, line);
            } else {
                lemma_unknown_stmts_is_refused(*f, line);
            }
        },
        Stmt::Unknown(_, _) => {},
    }
}

pub proof fn lemma_unknown_stmts_is_refused(ss: Stmts, line: u32)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts(ss, line).is_err(),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, line);
            } else {
                lemma_unknown_stmts_is_refused(*rest, line);
            }
        },
        Stmts::Nil => {},
    }
}

/// A body that holds a node with no rule is refused. The translator never skips one.
pub proof fn lemma_unknown_is_refused(f: Function)
    requires
        unknown_stmts(f.body),
    ensures
        spec_function(f).is_err(),
{
    lemma_unknown_stmts_is_refused(f.body, f.line);
}

pub open spec fn count_stmts(ss: Stmts) -> nat
    decreases ss,
{
    match ss {
        Stmts::Nil => 0,
        Stmts::Cons(s, rest) => count_stmt(*s) + count_stmts(*rest),
    }
}

pub open spec fn count_stmt(s: Stmt) -> nat
    decreases s,
{
    match s {
        Stmt::If(_, t, f) => 1 + count_stmts(*t) + count_stmts(*f),
        _ => 1,
    }
}

pub open spec fn count_dstmts(ss: DStmts) -> nat
    decreases ss,
{
    match ss {
        DStmts::Nil => 0,
        DStmts::Cons(s, rest) => count_dstmt(*s) + count_dstmts(*rest),
    }
}

pub open spec fn count_dstmt(s: DStmt) -> nat
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => 1 + count_dstmts(*t) + count_dstmts(*f),
        _ => 1,
    }
}

pub proof fn lemma_stmt_kept(s: Stmt, line: u32)
    requires
        spec_stmt(s, line).is_ok(),
    ensures
        count_dstmt(spec_stmt(s, line).unwrap()) == count_stmt(s),
    decreases s,
{
    match s {
        Stmt::If(c, t, f) => {
            lemma_statements_kept(*t, line);
            lemma_statements_kept(*f, line);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches included.
pub proof fn lemma_statements_kept(ss: Stmts, line: u32)
    requires
        spec_stmts(ss, line).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, line).unwrap()) == count_stmts(ss),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_kept(*s, line);
            lemma_statements_kept(*rest, line);
        },
        Stmts::Nil => {},
    }
}

// ------------------------------------------------------------------ the code that runs

pub fn translate_ty(t: Ty, line: u32) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_ty(t, line),
{
    match t {
        Ty::I32 => Ok(DTy::Int32),
        Ty::I64 => Ok(DTy::Int64),
        Ty::U8 => Ok(DTy::UInt8),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

pub fn translate_code(e: &Expr, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_code(*e, line),
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(*n)),
        Expr::Var(v, t) => match translate_ty(*t, line) {
            Ok(_) => Ok(DExpr::Var(*v)),
            Err(r) => Err(r),
        },
        Expr::Bin(op, a, b) => match translate_code(a, line) {
            Ok(da) => match translate_code(b, line) {
                Ok(db) => Ok(DExpr::Bin(*op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match translate_code(a, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match translate_code(a, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(*n, line)),
        Expr::Result => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn lookup(ps: &Params, name: u32) -> (r: Option<Ty>)
    ensures
        r == spec_lookup(*ps, name),
    decreases ps,
{
    match ps {
        Params::Nil => None,
        Params::Cons(n, t, rest) => if *n == name {
            Some(*t)
        } else {
            lookup(rest, name)
        },
    }
}

pub fn translate_leaf(d: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_leaf(d, t, line),
{
    match translate_ty(t, line) {
        Ok(_) => if t == Ty::I32 || t == Ty::I64 || t == Ty::U8 {
            Ok(DExpr::AsInt(Box::new(d)))
        } else {
            Ok(d)
        },
        Err(r) => Err(r),
    }
}

pub fn translate_contract(e: &Expr, ps: &Params, ret: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_contract(*e, *ps, ret, line),
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(*n)),
        Expr::Name(n) => match lookup(ps, *n) {
            Some(t) => translate_leaf(DExpr::Var(*n), t, line),
            None => Err(Refusal::Name(*n, line)),
        },
        Expr::Result => translate_leaf(DExpr::Result, ret, line),
        Expr::Bin(op, a, b) => match translate_contract(a, ps, ret, line) {
            Ok(da) => match translate_contract(b, ps, ret, line) {
                Ok(db) => Ok(DExpr::Bin(*op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match translate_contract(a, ps, ret, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match translate_contract(a, ps, ret, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Var(_, _) => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_stmt(s: &Stmt, line: u32) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_stmt(*s, line),
    decreases s,
{
    match s {
        Stmt::Return(e) => match translate_code(e, line) {
            Ok(d) => Ok(DStmt::Return(d)),
            Err(r) => Err(r),
        },
        Stmt::If(c, t, f) => match translate_code(c, line) {
            Ok(dc) => match translate_stmts(t, line) {
                Ok(dt) => match translate_stmts(f, line) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_stmts(ss: &Stmts, line: u32) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts(*ss, line),
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match translate_stmt(s, line) {
            Ok(d) => match translate_stmts(rest, line) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn translate_params(ps: &Params, line: u32) -> (r: Result<DParams, Refusal>)
    ensures
        r == spec_params(*ps, line),
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match translate_ty(*t, line) {
            Ok(dt) => match translate_params(rest, line) {
                Ok(dr) => Ok(DParams::Cons(*n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn translate_conds(cs: &Conds, want: CondKind, ps: &Params, ret: Ty) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_conds(*cs, want, *ps, ret),
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            _ => match translate_conds(rest, want, ps, ret) {
                Ok(dr) => if *k == want {
                    match translate_contract(e, ps, ret, *l) {
                        Ok(d) => Ok(DConds::Cons(d, Box::new(dr))),
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

/// The model of one function, or the reason the translator refuses it.
pub fn translate_function(f: &Function) -> (r: Result<Method, Refusal>)
    ensures
        r == spec_function(*f),
{
    match translate_params(&f.params, f.line) {
        Err(r) => Err(r),
        Ok(ps) => match translate_ty(f.ret, f.line) {
            Err(r) => Err(r),
            Ok(ret) => match translate_conds(&f.conds, CondKind::Requires, &f.params, f.ret) {
                Err(r) => Err(r),
                Ok(req) => match translate_conds(&f.conds, CondKind::Ensures, &f.params, f.ret) {
                    Err(r) => Err(r),
                    Ok(ens) => match translate_stmts(&f.body, f.line) {
                        Err(r) => Err(r),
                        Ok(body) => Ok(Method { name: f.name, params: ps, ret, requires: req, ensures: ens, body }),
                    },
                },
            },
        },
    }
}


// ------------------------------------------------------------------ the contract parser

/// A token of a contract line. The shell cuts the text into tokens. `Op` holds `- ` as `Sub`, and the parser reads it as a
/// negation where no operand is before it. `Unknown` is text with no token, by the id of its kind and its line.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Tok {
    Ident(u32),
    Int(i64),
    Result,
    Op(BinOp),
    Bang,
    LParen,
    RParen,
    Unknown(u32, u32),
}

/// What a parse gives: an expression, and the place of the first token it did not read. The place is past the start, and no
/// unknown node is in the expression.
pub open spec fn parsed(r: Result<(Expr, usize), Refusal>, toks: Seq<Tok>, pos: usize) -> bool {
    match r {
        Ok((e, p)) => pos < p && p <= toks.len() && !unknown_expr(e),
        Err(_) => true,
    }
}

fn is_cmp(op: BinOp) -> (b: bool) {
    match op {
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => true,
        _ => false,
    }
}

/// The precedence of the contract language, lowest first: `==>`, which groups to the right, then `||`, `&&`, a comparison, which
/// does not chain, `+` and `-`, `*`, and the prefix `!` and `-`. Parentheses group.
/// ponytail: the parser is proved to end and to read each token once, not to follow a grammar written as a spec. Upgrade: the
/// grammar as a spec relation, and a proof that each parse is in it.
fn parse_implies(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 7usize,
{
    let (a, p) = match parse_or(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if p < toks.len() && toks[p] == Tok::Op(BinOp::Implies) {
        match parse_implies(toks, p + 1, line) {
            Ok((b, q)) => Ok((Expr::Bin(BinOp::Implies, Box::new(a), Box::new(b)), q)),
            Err(e) => Err(e),
        }
    } else {
        Ok((a, p))
    }
}

fn parse_or(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 6usize,
{
    let (mut a, mut p) = match parse_and(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && toks[p] == Tok::Op(BinOp::Or)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_and(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::Or, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

fn parse_and(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 5usize,
{
    let (mut a, mut p) = match parse_cmp(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && toks[p] == Tok::Op(BinOp::And)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_cmp(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::And, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

fn parse_cmp(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 4usize,
{
    let (a, p) = match parse_add(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if p < toks.len() {
        if let Tok::Op(op) = toks[p] {
            if is_cmp(op) {
                return match parse_add(toks, p + 1, line) {
                    Ok((b, q)) => Ok((Expr::Bin(op, Box::new(a), Box::new(b)), q)),
                    Err(e) => Err(e),
                };
            }
        }
    }
    Ok((a, p))
}

fn parse_add(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 3usize,
{
    let (mut a, mut p) = match parse_mul(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && (toks[p] == Tok::Op(BinOp::Add) || toks[p] == Tok::Op(BinOp::Sub))
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        let op = if toks[p] == Tok::Op(BinOp::Add) {
            BinOp::Add
        } else {
            BinOp::Sub
        };
        match parse_mul(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(op, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

fn parse_mul(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 2usize,
{
    let (mut a, mut p) = match parse_unary(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && toks[p] == Tok::Op(BinOp::Mul)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_unary(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::Mul, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

fn parse_unary(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 1usize,
{
    if pos < toks.len() && toks[pos] == Tok::Bang {
        match parse_unary(toks, pos + 1, line) {
            Ok((a, p)) => Ok((Expr::Not(Box::new(a)), p)),
            Err(e) => Err(e),
        }
    } else if pos < toks.len() && toks[pos] == Tok::Op(BinOp::Sub) {
        match parse_unary(toks, pos + 1, line) {
            Ok((a, p)) => Ok((Expr::Neg(Box::new(a)), p)),
            Err(e) => Err(e),
        }
    } else {
        parse_primary(toks, pos, line)
    }
}

fn parse_primary(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 0usize,
{
    if pos >= toks.len() {
        return Err(Refusal::Syntax(line));
    }
    match toks[pos] {
        Tok::Int(n) => Ok((Expr::Int(n), pos + 1)),
        Tok::Ident(n) => Ok((Expr::Name(n), pos + 1)),
        Tok::Result => Ok((Expr::Result, pos + 1)),
        Tok::LParen => match parse_implies(toks, pos + 1, line) {
            Ok((e, p)) => if p < toks.len() && toks[p] == Tok::RParen {
                Ok((e, p + 1))
            } else {
                Err(Refusal::Syntax(line))
            },
            Err(e) => Err(e),
        },
        Tok::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

/// One contract line. It reads every token, or it refuses the line, and what it gives holds no unknown node.
pub fn parse_contract(toks: &Vec<Tok>, line: u32) -> (r: Result<Expr, Refusal>)
    ensures
        r matches Ok(e) ==> !unknown_expr(e),
{
    match parse_implies(toks, 0, line) {
        Ok((e, p)) => if p == toks.len() {
            Ok(e)
        } else {
            Err(Refusal::Syntax(line))
        },
        Err(e) => Err(e),
    }
}

} // verus!

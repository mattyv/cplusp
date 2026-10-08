//! The translator from the C++ subset to Dafny, decisions 0056, 0057 and 0058.
//!
//! The shell hands this module the compiler's tree of the functions of one file as plain data, and gets a model of each back. Each
//! rule of the translation is a spec function here, and each exec function is proved to compute exactly its spec. The proofs say:
//!
//! - `translate_unit` and `translate_function`: the result is the spec model, `spec_unit` and `spec_function`.
//! - a node that the translator does not know is refused, never skipped: `lemma_unknown_is_refused`.
//! - a translated body has one Dafny statement for each C++ statement: `lemma_statements_kept`.
//! - each call in a method names a function that has a method in the model: `lemma_calls_resolve`.
//! - `parse_contract`: it ends, it reads every token or refuses the line, and an expression it gives holds no unknown node.
//!
//! A Dafny expression has no call, so a call in a method stands alone by the shape of the types.
//! The lists are cons lists, so that each rule and each proof is one structural recursion.
//! Names, keys of functions, kinds of construct and lines are numbers. The shell keeps the table of names and prints the text.

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

/// A cast that the compiler made or the author wrote. `Read` is the read of a variable, an lvalue-to-rvalue cast, and `NoOp` changes
/// nothing. Both keep the value. `Integral` is a cast from one integral type to another, by both types. `Other` is a cast with no
/// rule yet, by the id of its kind.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CastKind {
    Read,
    NoOp,
    Integral(Ty, Ty),
    Other(u32),
}

/// An expression. In code, a name carries its type, which the compiler gave. In a contract, a name carries no type, and the
/// translator finds it among the parameters. `Brace` is a braced value of one scalar, such as `int64_t{a}`. `Call` is a call by the
/// key of its callee, the id of the callee's name for a refusal, its arguments and its line. `Unknown` is a construct with no rule,
/// by the id of its kind and its line.
#[derive(PartialEq, Eq, Debug)]
pub enum Expr {
    Int(i64),
    Var(u32, Ty),
    Name(u32),
    Result,
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    Cast(CastKind, Box<Expr>),
    Paren(Box<Expr>),
    Brace(Box<Expr>),
    Call(u32, u32, Box<Args>, u32),
    Unknown(u32, u32),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Args {
    Nil,
    Cons(Box<Expr>, Box<Args>),
}

/// A statement of the body, with its line. `Local` declares a name of a type with a start value.
#[derive(PartialEq, Eq, Debug)]
pub enum Stmt {
    Return(Expr, u32),
    If(Expr, Box<Stmts>, Box<Stmts>, u32),
    Local(u32, Ty, Expr, u32),
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

/// What a contract line says. `Other` is a word the translator has no rule for yet, by the id of the word. `Bad` is a line that the
/// shell could not cut or parse, with the refusal it got.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CondKind {
    Requires,
    Ensures,
    Other(u32),
    Bad(Refusal),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Conds {
    Nil,
    Cons(CondKind, Expr, u32, Box<Conds>),
}

/// One function: its key, its parameters, its return type, its contract and its body. The key names the function apart from every
/// other, overloads included. `line` is the line of its name.
#[derive(PartialEq, Eq, Debug)]
pub struct Function {
    pub name: u32,
    pub line: u32,
    pub params: Params,
    pub ret: Ty,
    pub conds: Conds,
    pub body: Stmts,
}

/// The functions of one file.
#[derive(PartialEq, Eq, Debug)]
pub enum Fns {
    Nil,
    Cons(Box<Function>, Box<Fns>),
}

// ------------------------------------------------------------------ the Dafny side

#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum DTy {
    Int32,
    Int64,
    UInt8,
    Bool,
}

/// A Dafny expression. `AsInt` is `(e as int)`, the exact value of a machine integer. `Conv` is `(e as T)`, which Dafny proves
/// fits `T`. A Dafny expression has no call.
#[derive(PartialEq, Eq, Debug)]
pub enum DExpr {
    Lit(i64),
    Var(u32),
    Result,
    Bin(BinOp, Box<DExpr>, Box<DExpr>),
    Not(Box<DExpr>),
    Neg(Box<DExpr>),
    AsInt(Box<DExpr>),
    Conv(DTy, Box<DExpr>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DArgs {
    Nil,
    Cons(DExpr, Box<DArgs>),
}

/// A Dafny statement. `Local` is `var x: T := e;`. `LocalCall` is `var x: T := m(args);`. `ReturnCall` is `result := m(args);
/// return;`, since Dafny takes no call in a `return`.
#[derive(PartialEq, Eq, Debug)]
pub enum DStmt {
    Return(DExpr),
    If(DExpr, Box<DStmts>, Box<DStmts>),
    Local(u32, DTy, DExpr),
    LocalCall(u32, DTy, u32, DArgs),
    ReturnCall(u32, DArgs),
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

/// The model of one function, decision 0058. `Full` is the method with its contract and body. `Bare` is a function whose signature
/// is in the subset and whose contract or body is refused: a method by key, parameters and return type, with no contract and no
/// body, so it assumes nothing, and the refusal. `Refused` is a function whose signature is not in the subset: no method.
#[derive(PartialEq, Eq, Debug)]
pub enum Model {
    Full(Method),
    Bare(u32, DParams, DTy, Refusal),
    Refused(Refusal),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Models {
    Nil,
    Cons(Model, Box<Models>),
}

/// Why the translator refused. `Construct` is a node with no rule: the id of its kind and its line. `Name` is a name in a contract
/// that is no parameter. `Syntax` is a contract line the parser cannot read. `Backslash` is a contract line that ends in a backslash.
/// `Callee` is a call to a function with no method, by the id of the callee's name. `Place` is a call that does not stand alone.
/// `Twice` is a name declared a second time in a function. `Convert` is a cast between `bool` and a number.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Refusal {
    Construct(u32, u32),
    Name(u32, u32),
    Syntax(u32),
    Backslash(u32),
    Callee(u32, u32),
    Place(u32),
    Twice(u32, u32),
    Convert(u32),
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

/// An integral cast, decision 0058. Both types must be in the subset, and neither may be `bool`. The cast is `(e as T)`, so Dafny
/// proves that the value fits `T`, and the model never wraps.
pub open spec fn spec_integral(from: Ty, to: Ty, d: DExpr, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(from, line) {
        Err(r) => Err(r),
        Ok(_) => match spec_ty(to, line) {
            Err(r) => Err(r),
            Ok(dto) => if from == Ty::Bool || to == Ty::Bool {
                Err(Refusal::Convert(line))
            } else {
                Ok(DExpr::Conv(dto, Box::new(d)))
            },
        },
    }
}

/// An expression of the body. The operators stay the machine operators of their newtype, so Dafny checks each step for
/// overflow, the battery case signed_overflow. A contract name or `result` has no place in code. A call here does not stand alone.
/// `line` is the line of the statement.
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
        Expr::Cast(c, a) => match c {
            CastKind::Other(k) => Err(Refusal::Construct(k, line)),
            CastKind::Integral(from, to) => match spec_code(*a, line) {
                Ok(da) => spec_integral(from, to, da, line),
                Err(r) => Err(r),
            },
            _ => spec_code(*a, line),
        },
        Expr::Paren(a) => spec_code(*a, line),
        Expr::Brace(a) => spec_code(*a, line),
        Expr::Call(_, _, _, l) => Err(Refusal::Place(l)),
        Expr::Name(n) => Err(Refusal::Name(n, line)),
        Expr::Result => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// The arguments of a call, each an expression of code. So an argument holds no call.
pub open spec fn spec_args(args: Args, line: u32) -> Result<DArgs, Refusal>
    decreases args,
{
    match args {
        Args::Nil => Ok(DArgs::Nil),
        Args::Cons(a, rest) => match spec_code(*a, line) {
            Ok(da) => match spec_args(*rest, line) {
                Ok(dr) => Ok(DArgs::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
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
        Expr::Paren(a) => spec_contract(*a, ps, ret, line),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

/// The parameters as Dafny parameters.
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

/// A function has a method when its parameters and its return type are in the subset.
pub open spec fn has_signature(f: Function) -> bool {
    spec_params(f.params, f.line).is_ok() && spec_ty(f.ret, f.line).is_ok()
}

/// A key names a function of the file that has a method.
pub open spec fn spec_callable(fs: Fns, key: u32) -> bool
    decreases fs,
{
    match fs {
        Fns::Nil => false,
        Fns::Cons(f, rest) => (f.name == key && has_signature(*f)) || spec_callable(*rest, key),
    }
}

/// A call that stands alone, decision 0058: its callee has a method, and its arguments translate. `line` is the line of the
/// statement, and `at` is the line of the call.
pub open spec fn spec_call(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32) -> Result<DArgs, Refusal> {
    if spec_callable(all, key) {
        spec_args(args, line)
    } else {
        Err(Refusal::Callee(name, at))
    }
}

/// A statement of the body, and a list of them. A call is in a statement only as the full value of a `return` or the full start
/// value of a local.
// ponytail: `return (f(x));` is refused as a call inside an expression. Upgrade: look through parentheses.
pub open spec fn spec_stmt(s: Stmt, all: Fns) -> Result<DStmt, Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e, l) => match e {
            Expr::Call(k, n, args, at) => match spec_call(k, n, *args, at, all, l) {
                Ok(da) => Ok(DStmt::ReturnCall(k, da)),
                Err(r) => Err(r),
            },
            _ => match spec_code(e, l) {
                Ok(d) => Ok(DStmt::Return(d)),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match spec_code(c, l) {
            Ok(dc) => match spec_stmts(*t, all) {
                Ok(dt) => match spec_stmts(*f, all) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match spec_ty(t, l) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => match spec_call(k, nm, *args, at, all, l) {
                    Ok(da) => Ok(DStmt::LocalCall(n, dt, k, da)),
                    Err(r) => Err(r),
                },
                _ => match spec_code(e, l) {
                    Ok(d) => Ok(DStmt::Local(n, dt, d)),
                    Err(r) => Err(r),
                },
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

pub open spec fn spec_stmts(ss: Stmts, all: Fns) -> Result<DStmts, Refusal>
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match spec_stmt(*s, all) {
            Ok(d) => match spec_stmts(*rest, all) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The lines of one kind of the contract, in their order. A word with no rule, or a line the shell could not read, is refused.
pub open spec fn spec_conds(cs: Conds, want: CondKind, ps: Params, ret: Ty) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
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

/// Each name is declared once in a function, decision 0058. `seen` holds the names declared before, in the order of the source.
/// Each rule gives the first name declared a second time, with the line of that declaration, and the names seen after it.
pub open spec fn spec_twice_params(seen: Seq<u32>, ps: Params, line: u32) -> (Option<(u32, u32)>, Seq<u32>)
    decreases ps,
{
    match ps {
        Params::Nil => (None, seen),
        Params::Cons(n, _, rest) => if seen.contains(n) {
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
        _ => (None, seen),
    }
}

pub open spec fn spec_twice_stmts(seen: Seq<u32>, ss: Stmts) -> (Option<(u32, u32)>, Seq<u32>)
    decreases ss,
{
    match ss {
        Stmts::Nil => (None, seen),
        Stmts::Cons(s, rest) => {
            let (r, after) = spec_twice_stmt(seen, *s);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_stmts(after, *rest)
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

/// The contract and the body of a function whose signature is in the subset: the requires lines, the ensures lines and the body.
pub open spec fn spec_inside(f: Function, all: Fns) -> Result<(DConds, DConds, DStmts), Refusal> {
    match spec_conds(f.conds, CondKind::Requires, f.params, f.ret) {
        Err(r) => Err(r),
        Ok(req) => match spec_conds(f.conds, CondKind::Ensures, f.params, f.ret) {
            Err(r) => Err(r),
            Ok(ens) => match spec_twice(f) {
                Some((n, l)) => Err(Refusal::Twice(n, l)),
                None => match spec_stmts(f.body, all) {
                    Err(r) => Err(r),
                    Ok(body) => Ok((req, ens, body)),
                },
            },
        },
    }
}

/// The model of a function among the functions `all` of its file, decision 0058.
pub open spec fn spec_function(f: Function, all: Fns) -> Model {
    match spec_params(f.params, f.line) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match spec_ty(f.ret, f.line) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match spec_inside(f, all) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, body)) => Model::Full(Method { name: f.name, params: ps, ret, requires: req, ensures: ens, body }),
            },
        },
    }
}

/// The models of the functions `fs`, each among the functions `all` of the file.
pub open spec fn spec_unit(fs: Fns, all: Fns) -> Models
    decreases fs,
{
    match fs {
        Fns::Nil => Models::Nil,
        Fns::Cons(f, rest) => Models::Cons(spec_function(*f, all), Box::new(spec_unit(*rest, all))),
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
        Expr::Cast(_, a) => unknown_expr(*a),
        Expr::Paren(a) => unknown_expr(*a),
        Expr::Brace(a) => unknown_expr(*a),
        Expr::Call(_, _, args, _) => unknown_args(*args),
        _ => false,
    }
}

pub open spec fn unknown_args(args: Args) -> bool
    decreases args,
{
    match args {
        Args::Nil => false,
        Args::Cons(a, rest) => unknown_expr(*a) || unknown_args(*rest),
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
        Expr::Cast(_, a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Paren(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Brace(a) => lemma_unknown_code_is_refused(*a, line),
        _ => {},
    }
}

pub proof fn lemma_unknown_args_is_refused(args: Args, line: u32)
    requires
        unknown_args(args),
    ensures
        spec_args(args, line).is_err(),
    decreases args,
{
    match args {
        Args::Cons(a, rest) => {
            if unknown_expr(*a) {
                lemma_unknown_code_is_refused(*a, line);
            } else {
                lemma_unknown_args_is_refused(*rest, line);
            }
        },
        Args::Nil => {},
    }
}

pub proof fn lemma_unknown_call_is_refused(e: Expr, all: Fns, line: u32)
    requires
        unknown_expr(e),
        e is Call,
    ensures
        spec_call(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line).is_err(),
{
    if spec_callable(all, e->Call_0) {
        lemma_unknown_args_is_refused(*e->Call_2, line);
    }
}

pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all).is_err(),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::If(c, t, f, l) => {
            if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else if unknown_stmts(*t) {
                lemma_unknown_stmts_is_refused(*t, all);
            } else {
                lemma_unknown_stmts_is_refused(*f, all);
            }
        },
        Stmt::Local(_, _, e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::Unknown(_, _) => {},
    }
}

pub proof fn lemma_unknown_stmts_is_refused(ss: Stmts, all: Fns)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts(ss, all).is_err(),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all);
            } else {
                lemma_unknown_stmts_is_refused(*rest, all);
            }
        },
        Stmts::Nil => {},
    }
}

/// A body that holds a node with no rule never gives a full model. The translator never skips one.
pub proof fn lemma_unknown_is_refused(f: Function, all: Fns)
    requires
        unknown_stmts(f.body),
    ensures
        !(spec_function(f, all) is Full),
{
    lemma_unknown_stmts_is_refused(f.body, all);
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
        Stmt::If(_, t, f, _) => 1 + count_stmts(*t) + count_stmts(*f),
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

pub proof fn lemma_stmt_kept(s: Stmt, all: Fns)
    requires
        spec_stmt(s, all).is_ok(),
    ensures
        count_dstmt(spec_stmt(s, all).unwrap()) == count_stmt(s),
    decreases s,
{
    match s {
        Stmt::If(c, t, f, _) => {
            lemma_statements_kept(*t, all);
            lemma_statements_kept(*f, all);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches included.
pub proof fn lemma_statements_kept(ss: Stmts, all: Fns)
    requires
        spec_stmts(ss, all).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, all).unwrap()) == count_stmts(ss),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_kept(*s, all);
            lemma_statements_kept(*rest, all);
        },
        Stmts::Nil => {},
    }
}

/// The models hold a method, full or bare, with this key.
pub open spec fn has_method(ms: Models, key: u32) -> bool
    decreases ms,
{
    match ms {
        Models::Nil => false,
        Models::Cons(m, rest) => match m {
            Model::Full(method) => method.name == key || has_method(*rest, key),
            Model::Bare(name, _, _, _) => name == key || has_method(*rest, key),
            Model::Refused(_) => has_method(*rest, key),
        },
    }
}

/// Each call of the statements names a key of `all` that has a method.
pub open spec fn calls_resolve(ss: DStmts, all: Fns) -> bool
    decreases ss,
{
    match ss {
        DStmts::Nil => true,
        DStmts::Cons(s, rest) => calls_resolve_stmt(*s, all) && calls_resolve(*rest, all),
    }
}

pub open spec fn calls_resolve_stmt(s: DStmt, all: Fns) -> bool
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => calls_resolve(*t, all) && calls_resolve(*f, all),
        DStmt::LocalCall(_, _, k, _) => spec_callable(all, k),
        DStmt::ReturnCall(k, _) => spec_callable(all, k),
        _ => true,
    }
}

pub proof fn lemma_stmt_calls_resolve(s: Stmt, all: Fns)
    requires
        spec_stmt(s, all).is_ok(),
    ensures
        calls_resolve_stmt(spec_stmt(s, all).unwrap(), all),
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => {
            lemma_stmts_calls_resolve(*t, all);
            lemma_stmts_calls_resolve(*f, all);
        },
        _ => {},
    }
}

pub proof fn lemma_stmts_calls_resolve(ss: Stmts, all: Fns)
    requires
        spec_stmts(ss, all).is_ok(),
    ensures
        calls_resolve(spec_stmts(ss, all).unwrap(), all),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all);
            lemma_stmts_calls_resolve(*rest, all);
        },
        Stmts::Nil => {},
    }
}

/// A key with a signature in the subset has a method among the models of the file.
pub proof fn lemma_callable_has_method(fs: Fns, all: Fns, key: u32)
    requires
        spec_callable(fs, key),
    ensures
        has_method(spec_unit(fs, all), key),
    decreases fs,
{
    match fs {
        Fns::Cons(f, rest) => {
            if !(f.name == key && has_signature(*f)) {
                lemma_callable_has_method(*rest, all, key);
            }
        },
        Fns::Nil => {},
    }
}

/// Each call in a full method of the file names a method of the model of the file, so the Dafny file resolves.
pub proof fn lemma_calls_resolve(f: Function, all: Fns)
    requires
        spec_function(f, all) is Full,
    ensures
        calls_resolve(spec_function(f, all)->Full_0.body, all),
        forall|k: u32| spec_callable(all, k) ==> #[trigger] has_method(spec_unit(all, all), k),
{
    lemma_stmts_calls_resolve(f.body, all);
    assert forall|k: u32| spec_callable(all, k) implies #[trigger] has_method(spec_unit(all, all), k) by {
        lemma_callable_has_method(all, all, k);
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

pub fn translate_integral(from: Ty, to: Ty, d: DExpr, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_integral(from, to, d, line),
{
    match translate_ty(from, line) {
        Err(r) => Err(r),
        Ok(_) => match translate_ty(to, line) {
            Err(r) => Err(r),
            Ok(dto) => if from == Ty::Bool || to == Ty::Bool {
                Err(Refusal::Convert(line))
            } else {
                Ok(DExpr::Conv(dto, Box::new(d)))
            },
        },
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
        Expr::Cast(c, a) => match c {
            CastKind::Other(k) => Err(Refusal::Construct(*k, line)),
            CastKind::Integral(from, to) => match translate_code(a, line) {
                Ok(da) => translate_integral(*from, *to, da, line),
                Err(r) => Err(r),
            },
            _ => translate_code(a, line),
        },
        Expr::Paren(a) => translate_code(a, line),
        Expr::Brace(a) => translate_code(a, line),
        Expr::Call(_, _, _, l) => Err(Refusal::Place(*l)),
        Expr::Name(n) => Err(Refusal::Name(*n, line)),
        Expr::Result => Err(Refusal::Syntax(line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_args(args: &Args, line: u32) -> (r: Result<DArgs, Refusal>)
    ensures
        r == spec_args(*args, line),
    decreases args,
{
    match args {
        Args::Nil => Ok(DArgs::Nil),
        Args::Cons(a, rest) => match translate_code(a, line) {
            Ok(da) => match translate_args(rest, line) {
                Ok(dr) => Ok(DArgs::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
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
        Expr::Paren(a) => translate_contract(a, ps, ret, line),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
        _ => Err(Refusal::Syntax(line)),
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

pub fn signature(f: &Function) -> (r: bool)
    ensures
        r == has_signature(*f),
{
    translate_params(&f.params, f.line).is_ok() && translate_ty(f.ret, f.line).is_ok()
}

pub fn callable(fs: &Fns, key: u32) -> (r: bool)
    ensures
        r == spec_callable(*fs, key),
    decreases fs,
{
    match fs {
        Fns::Nil => false,
        Fns::Cons(f, rest) => (f.name == key && signature(f)) || callable(rest, key),
    }
}

pub fn translate_call(key: u32, name: u32, args: &Args, at: u32, all: &Fns, line: u32) -> (r: Result<DArgs, Refusal>)
    ensures
        r == spec_call(key, name, *args, at, *all, line),
{
    if callable(all, key) {
        translate_args(args, line)
    } else {
        Err(Refusal::Callee(name, at))
    }
}

pub fn translate_stmt(s: &Stmt, all: &Fns) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_stmt(*s, *all),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => match e {
            Expr::Call(k, n, args, at) => match translate_call(*k, *n, args, *at, all, *l) {
                Ok(da) => Ok(DStmt::ReturnCall(*k, da)),
                Err(r) => Err(r),
            },
            _ => match translate_code(e, *l) {
                Ok(d) => Ok(DStmt::Return(d)),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match translate_code(c, *l) {
            Ok(dc) => match translate_stmts(t, all) {
                Ok(dt) => match translate_stmts(f, all) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match translate_ty(*t, *l) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => match translate_call(*k, *nm, args, *at, all, *l) {
                    Ok(da) => Ok(DStmt::LocalCall(*n, dt, *k, da)),
                    Err(r) => Err(r),
                },
                _ => match translate_code(e, *l) {
                    Ok(d) => Ok(DStmt::Local(*n, dt, d)),
                    Err(r) => Err(r),
                },
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_stmts(ss: &Stmts, all: &Fns) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts(*ss, *all),
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match translate_stmt(s, all) {
            Ok(d) => match translate_stmts(rest, all) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), Box::new(dr))),
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
            CondKind::Bad(r) => Err(*r),
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

/// `seen` holds `x`.
pub fn holds(seen: &Vec<u32>, x: u32) -> (r: bool)
    ensures
        r == seen@.contains(x),
{
    let mut i: usize = 0;
    while i < seen.len()
        invariant
            i <= seen.len(),
            forall|j: int| 0 <= j < i ==> seen@[j] != x,
        decreases seen.len() - i,
    {
        if seen[i] == x {
            assert(seen@[i as int] == x);
            return true;
        }
        i += 1;
    }
    false
}

pub fn twice_params(seen: &mut Vec<u32>, ps: &Params, line: u32) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice_params(old(seen)@, *ps, line).0,
        final(seen)@ == spec_twice_params(old(seen)@, *ps, line).1,
    decreases ps,
{
    match ps {
        Params::Nil => None,
        Params::Cons(n, _, rest) => if holds(seen, *n) {
            Some((*n, line))
        } else {
            seen.push(*n);
            twice_params(seen, rest, line)
        },
    }
}

pub fn twice_stmt(seen: &mut Vec<u32>, s: &Stmt) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice_stmt(old(seen)@, *s).0,
        final(seen)@ == spec_twice_stmt(old(seen)@, *s).1,
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, l) => if holds(seen, *n) {
            Some((*n, *l))
        } else {
            seen.push(*n);
            None
        },
        Stmt::If(_, t, f, _) => {
            let r = twice_stmts(seen, t);
            if r.is_some() {
                r
            } else {
                twice_stmts(seen, f)
            }
        },
        _ => None,
    }
}

pub fn twice_stmts(seen: &mut Vec<u32>, ss: &Stmts) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice_stmts(old(seen)@, *ss).0,
        final(seen)@ == spec_twice_stmts(old(seen)@, *ss).1,
    decreases ss,
{
    match ss {
        Stmts::Nil => None,
        Stmts::Cons(s, rest) => {
            let r = twice_stmt(seen, s);
            if r.is_some() {
                r
            } else {
                twice_stmts(seen, rest)
            }
        },
    }
}

pub fn twice(f: &Function) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice(*f),
{
    let mut seen: Vec<u32> = Vec::new();
    assert(seen@ =~= Seq::<u32>::empty());
    let r = twice_params(&mut seen, &f.params, f.line);
    if r.is_some() {
        r
    } else {
        twice_stmts(&mut seen, &f.body)
    }
}

pub fn translate_inside(f: &Function, all: &Fns) -> (r: Result<(DConds, DConds, DStmts), Refusal>)
    ensures
        r == spec_inside(*f, *all),
{
    match translate_conds(&f.conds, CondKind::Requires, &f.params, f.ret) {
        Err(r) => Err(r),
        Ok(req) => match translate_conds(&f.conds, CondKind::Ensures, &f.params, f.ret) {
            Err(r) => Err(r),
            Ok(ens) => match twice(f) {
                Some((n, l)) => Err(Refusal::Twice(n, l)),
                None => match translate_stmts(&f.body, all) {
                    Err(r) => Err(r),
                    Ok(body) => Ok((req, ens, body)),
                },
            },
        },
    }
}

/// The model of one function among the functions `all` of its file.
pub fn translate_function(f: &Function, all: &Fns) -> (r: Model)
    ensures
        r == spec_function(*f, *all),
{
    match translate_params(&f.params, f.line) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match translate_ty(f.ret, f.line) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match translate_inside(f, all) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, body)) => Model::Full(Method { name: f.name, params: ps, ret, requires: req, ensures: ens, body }),
            },
        },
    }
}

fn translate_each(fs: &Fns, all: &Fns) -> (r: Models)
    ensures
        r == spec_unit(*fs, *all),
    decreases fs,
{
    match fs {
        Fns::Nil => Models::Nil,
        Fns::Cons(f, rest) => Models::Cons(translate_function(f, all), Box::new(translate_each(rest, all))),
    }
}

/// The models of the functions of one file, in their order.
pub fn translate_unit(all: &Fns) -> (r: Models)
    ensures
        r == spec_unit(*all, *all),
{
    translate_each(all, all)
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
/// Parse one contract line. A token with no rule refuses the line by its kind, wherever it is, before the grammar runs: the first
/// such token names the problem.
pub fn parse_contract(toks: &Vec<Tok>, line: u32) -> (r: Result<Expr, Refusal>)
    ensures
        r matches Ok(e) ==> !unknown_expr(e) && forall|i: int| 0 <= i < toks@.len() ==> !(toks@[i] is Unknown),
        forall|i: int|
            0 <= i < toks@.len() && #[trigger] toks@[i] is Unknown && (forall|j: int| 0 <= j < i ==> !(toks@[j] is Unknown)) ==> r
                == Err::<Expr, Refusal>(Refusal::Construct(toks@[i]->Unknown_0, toks@[i]->Unknown_1)),
{
    let mut i: usize = 0;
    while i < toks.len()
        invariant
            i <= toks.len(),
            forall|j: int| 0 <= j < i ==> !(toks@[j] is Unknown),
        decreases toks.len() - i,
    {
        if let Tok::Unknown(k, l) = toks[i] {
            return Err(Refusal::Construct(k, l));
        }
        i += 1;
    }
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

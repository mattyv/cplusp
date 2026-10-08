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

/// A scalar type, the element of a sequence, decision 0064.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Scalar {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
}

/// A type of the subset. `Seq` is a read-only sequence of a scalar, a parameter only, decision 0064. `Other` is a type the
/// translator has no rule for, by the id of its name.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Ty {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Seq(Scalar),
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

/// An expression. In code, a name and a literal carry their type, which the compiler gave, decision 0060. A literal is never
/// negative, since a minus is an operator, so it holds the full range of `uint64_t`, decision 0063. `Bool` is `true` or `false`. In a contract, a name
/// carries no type, and the translator finds it among the parameters, and `Int` is an exact integer. `Brace` is a braced value of one scalar, such as `int64_t{a}`. `Call` is a call by the
/// key of its callee, the id of the callee's name for a refusal, its arguments and its line. `Unknown` is a construct with no rule,
/// by the id of its kind and its line.
#[derive(PartialEq, Eq, Debug)]
pub enum Expr {
    Int(u64),
    Lit(u64, Ty),
    Bool(bool),
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
    Size(Box<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Forall(u32, Box<Expr>),
    Chain(BinOp, BinOp, Box<Expr>, Box<Expr>, Box<Expr>),
    Unknown(u32, u32),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Args {
    Nil,
    Cons(Box<Expr>, Box<Args>),
}

/// A statement of the body, with its line. `Local` declares a name of a type with a start value. `Assign` writes a name. `Step`
/// adds one to a name of a type, or takes one away when its flag is false. `While` is a condition, the contract lines above the loop
/// and the body. `For` is a start, a condition, a step, the contract lines and the body, decision 0061.
#[derive(PartialEq, Eq, Debug)]
pub enum Stmt {
    Return(Expr, u32),
    If(Expr, Box<Stmts>, Box<Stmts>, u32),
    Local(u32, Ty, Expr, u32),
    Assign(u32, Expr, u32),
    Step(u32, Ty, bool, u32),
    While(Expr, Box<Conds>, Box<Stmts>, u32),
    For(Box<Stmt>, Expr, Box<Stmt>, Box<Conds>, Box<Stmts>, u32),
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
    Invariant,
    Decreases,
    Other(u32),
    Bad(Refusal),
}

/// The names of the parameters of a declaration, in their order.
#[derive(PartialEq, Eq, Debug)]
pub enum Names {
    Nil,
    Cons(u32, Box<Names>),
}

/// A contract line: what it says, its expression, its line, and the names of the parameters of the declaration it stands on,
/// decision 0060.
#[derive(PartialEq, Eq, Debug)]
pub enum Conds {
    Nil,
    Cons(CondKind, Expr, u32, Names, Box<Conds>),
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
    UInt32,
    UInt64,
    Bool,
    Seq(Scalar),
}

/// A Dafny expression. `AsInt` is `(e as int)`, the exact value of a machine integer. `Conv` is `(e as T)`, which Dafny proves
/// fits `T`. A Dafny expression has no call.
#[derive(PartialEq, Eq, Debug)]
pub enum DExpr {
    Lit(u64),
    Bool(bool),
    Var(u32),
    Result,
    Bin(BinOp, Box<DExpr>, Box<DExpr>),
    Not(Box<DExpr>),
    Neg(Box<DExpr>),
    AsInt(Box<DExpr>),
    Conv(DTy, Box<DExpr>),
    Len(Box<DExpr>),
    Index(Box<DExpr>, Box<DExpr>),
    Forall(u32, Box<DExpr>),
    Bound(u32),
    Chain(BinOp, BinOp, Box<DExpr>, Box<DExpr>, Box<DExpr>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DArgs {
    Nil,
    Cons(DExpr, Box<DArgs>),
}

/// A Dafny statement. `Local` is `var x: T := e;`. `LocalCall` is `var x: T := m(args);`. `ReturnCall` is `result := m(args);
/// return;`, since Dafny takes no call in a `return`. `Assign` is `x := e;` and `AssignCall` is `x := m(args);`. `While` is the
/// condition, the invariants, the decreases lines and the body. `For` prints as its start, then a `while` whose body ends with the
/// step.
#[derive(PartialEq, Eq, Debug)]
pub enum DStmt {
    Return(DExpr),
    If(DExpr, Box<DStmts>, Box<DStmts>),
    Local(u32, DTy, DExpr),
    LocalCall(u32, DTy, u32, DArgs),
    ReturnCall(u32, DArgs),
    Assign(u32, DExpr),
    AssignCall(u32, u32, DArgs),
    While(DExpr, DConds, DConds, Box<DStmts>),
    For(Box<DStmt>, DExpr, DConds, DConds, Box<DStmts>, Box<DStmt>),
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
/// `Twice` is a name declared a second time in a function. `Convert` is a cast between `bool` and a number. `WriteParam` is a write
/// to a parameter. `NoVar` is a name in a loop contract that is no variable. `Misplaced` is a contract line in the wrong place.
/// `SeqParam` is a sequence that is no parameter.
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
    WriteParam(u32, u32),
    NoVar(u32, u32),
    Misplaced(u32),
    SeqParam(u32),
}

// ------------------------------------------------------------------ the rules

/// A type of the subset maps to its Dafny newtype, decision 0029 and the battery case signed_overflow.
pub open spec fn spec_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::I32 => Ok(DTy::Int32),
        Ty::I64 => Ok(DTy::Int64),
        Ty::U8 => Ok(DTy::UInt8),
        Ty::U32 => Ok(DTy::UInt32),
        Ty::U64 => Ok(DTy::UInt64),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(s) => Ok(DTy::Seq(s)),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

/// A type of a local or of a result: a type of the subset that is no sequence, decision 0064.
pub open spec fn spec_value_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::Seq(_) => Err(Refusal::SeqParam(line)),
        _ => spec_ty(t, line),
    }
}

/// The type of an element of a sequence.
pub open spec fn spec_elem(s: Scalar) -> Ty {
    match s {
        Scalar::I32 => Ty::I32,
        Scalar::I64 => Ty::I64,
        Scalar::U8 => Ty::U8,
        Scalar::U32 => Ty::U32,
        Scalar::U64 => Ty::U64,
        Scalar::Bool => Ty::Bool,
    }
}

/// Two comparisons that chain, as in Dafny: both up or both down.
pub open spec fn chains(a: BinOp, b: BinOp) -> bool {
    ((a == BinOp::Lt || a == BinOp::Le) && (b == BinOp::Lt || b == BinOp::Le)) || ((a == BinOp::Gt || a == BinOp::Ge) && (b
        == BinOp::Gt || b == BinOp::Ge))
}

/// An integer type, whose value a contract reads as an exact integer.
pub open spec fn is_integer(t: Ty) -> bool {
    t == Ty::I32 || t == Ty::I64 || t == Ty::U8 || t == Ty::U32 || t == Ty::U64
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
        Expr::Lit(n, t) => match spec_ty(t, line) {
            Ok(dt) => Ok(DExpr::Conv(dt, Box::new(DExpr::Lit(n)))),
            Err(r) => Err(r),
        },
        Expr::Bool(b) => Ok(DExpr::Bool(b)),
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
        Expr::Size(o) => match spec_code(*o, line) {
            Ok(d) => Ok(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(d))))),
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match spec_code(*o, line) {
            Ok(d) => match spec_code(*i, line) {
                Ok(di) => Ok(DExpr::Index(Box::new(d), Box::new(di))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(n, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
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

/// The parameter of the definition at the place where the declaration `decl` has the name `name`, decision 0060.
pub open spec fn spec_rebind(decl: Names, ps: Params, name: u32) -> Option<(u32, Ty)>
    decreases ps,
{
    match decl {
        Names::Nil => None,
        Names::Cons(d, drest) => match ps {
            Params::Nil => None,
            Params::Cons(p, t, prest) => if d == name {
                Some((p, t))
            } else {
                spec_rebind(*drest, *prest, name)
            },
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
/// `result` read as `as int`, so no step can overflow. A name bound by a `forall` in `bound` is an exact integer. Any other name
/// must be a parameter of the declaration `decl`, and it reads the parameter of the definition at its place. A loop contract has
/// no `ret`, so `result` has no place in it, and a name it does not find is no variable. `v.size()` and `v[e]` read a sequence
/// parameter, and a chain is two comparisons in one direction, decision 0064.
pub open spec fn spec_contract(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32) -> Result<DExpr, Refusal>
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(n)),
        Expr::Name(n) => if spec_has(bound, n) {
            Ok(DExpr::Bound(n))
        } else {
            match spec_rebind(decl, ps, n) {
                Some((p, t)) => spec_leaf(DExpr::Var(p), t, line),
                None => spec_unnamed(n, ret, line),
            }
        },
        Expr::Result => match ret {
            Some(t) => spec_leaf(DExpr::Result, t, line),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Bin(op, a, b) => match spec_contract(*a, decl, ps, ret, bound, line) {
            Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line) {
                Ok(db) => Ok(DExpr::Bin(op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match spec_contract(*a, decl, ps, ret, bound, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match spec_contract(*a, decl, ps, ret, bound, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Paren(a) => spec_contract(*a, decl, ps, ret, bound, line),
        Expr::Size(o) => match spec_seq_name(*o, decl, ps, ret, bound, line) {
            Ok((p, _)) => Ok(DExpr::Len(Box::new(DExpr::Var(p)))),
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match spec_seq_name(*o, decl, ps, ret, bound, line) {
            Ok((p, s)) => match spec_contract(*i, decl, ps, ret, bound, line) {
                Ok(di) => spec_leaf(DExpr::Index(Box::new(DExpr::Var(p)), Box::new(di)), spec_elem(s), line),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Forall(j, body) => match spec_contract(*body, decl, ps, ret, Names::Cons(j, Box::new(bound)), line) {
            Ok(db) => Ok(DExpr::Forall(j, Box::new(db))),
            Err(r) => Err(r),
        },
        Expr::Chain(o1, o2, a, b, c) => if chains(o1, o2) {
            match spec_contract(*a, decl, ps, ret, bound, line) {
                Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line) {
                    Ok(db) => match spec_contract(*c, decl, ps, ret, bound, line) {
                        Ok(dc) => Ok(DExpr::Chain(o1, o2, Box::new(da), Box::new(db), Box::new(dc))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

/// `name` is bound.
pub open spec fn spec_has(bound: Names, name: u32) -> bool
    decreases bound,
{
    match bound {
        Names::Nil => false,
        Names::Cons(n, rest) => n == name || spec_has(*rest, name),
    }
}

/// A name that is no parameter: of the contract of a function, or no variable of a loop contract.
pub open spec fn spec_unnamed(n: u32, ret: Option<Ty>, line: u32) -> Result<DExpr, Refusal> {
    match ret {
        Some(_) => Err(Refusal::Name(n, line)),
        None => Err(Refusal::NoVar(n, line)),
    }
}

/// The sequence that `v.size()` or `v[e]` reads: a name, not bound, of a parameter of sequence type, with its element.
pub open spec fn spec_seq_name(o: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32) -> Result<(u32, Scalar), Refusal> {
    match o {
        Expr::Name(n) => if spec_has(bound, n) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_rebind(decl, ps, n) {
                Some((p, Ty::Seq(s))) => Ok((p, s)),
                Some(_) => Err(Refusal::Syntax(line)),
                None => match ret {
                    Some(_) => Err(Refusal::Name(n, line)),
                    None => Err(Refusal::NoVar(n, line)),
                },
            }
        },
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
    spec_params(f.params, f.line).is_ok() && spec_value_ty(f.ret, f.line).is_ok()
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

/// The variables in scope after a statement, decision 0062: a local adds its name and type in front of the variables before it.
/// A local inside a branch or a loop body stays inside, so the scope after any other statement is the scope before it.
pub open spec fn spec_scope(s: Stmt, env: Params) -> Params {
    match s {
        Stmt::Local(n, t, _, _) => Params::Cons(n, t, Box::new(env)),
        _ => env,
    }
}

/// The names of a list of variables, in order.
pub open spec fn spec_names_of(ps: Params) -> Names
    decreases ps,
{
    match ps {
        Params::Nil => Names::Nil,
        Params::Cons(n, _, rest) => Names::Cons(n, Box::new(spec_names_of(*rest))),
    }
}

/// `name` is a parameter.
pub open spec fn spec_is_param(ps: Params, name: u32) -> bool
    decreases ps,
{
    match ps {
        Params::Nil => false,
        Params::Cons(n, _, rest) => n == name || spec_is_param(*rest, name),
    }
}

/// The lines of one kind of the contract of a loop, in their order, decisions 0061 and 0062. Each reads the variables `env` in scope
/// at the loop, and has no
/// `result`. A `requires` or an `ensures` line has no place above a loop.
pub open spec fn spec_loop_conds(cs: Conds, want: CondKind, env: Params) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, _, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Requires => Err(Refusal::Misplaced(l)),
            CondKind::Ensures => Err(Refusal::Misplaced(l)),
            _ => match spec_loop_conds(*rest, want, env) {
                Ok(dr) => if k == want {
                    match spec_contract(e, spec_names_of(env), env, None, Names::Nil, l) {
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

/// A statement of the body, and a list of them. `env` is the variables in scope, and `ps` the parameters. A call is in a
/// statement only as the full value of a `return`, of a local or of a write. A write is to a local, never to a parameter.
// ponytail: `return (f(x));` is refused as a call inside an expression. Upgrade: look through parentheses.
pub open spec fn spec_stmt(s: Stmt, all: Fns, env: Params, ps: Params) -> Result<DStmt, Refusal>
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
            Ok(dc) => match spec_stmts(*t, all, env, ps) {
                Ok(dt) => match spec_stmts(*f, all, env, ps) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match spec_value_ty(t, l) {
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
        Stmt::Assign(n, e, l) => if spec_is_param(ps, n) {
            Err(Refusal::WriteParam(n, l))
        } else {
            match e {
                Expr::Call(k, nm, args, at) => match spec_call(k, nm, *args, at, all, l) {
                    Ok(da) => Ok(DStmt::AssignCall(n, k, da)),
                    Err(r) => Err(r),
                },
                _ => match spec_code(e, l) {
                    Ok(d) => Ok(DStmt::Assign(n, d)),
                    Err(r) => Err(r),
                },
            }
        },
        Stmt::Step(n, t, up, l) => if spec_is_param(ps, n) {
            Err(Refusal::WriteParam(n, l))
        } else {
            match spec_ty(t, l) {
                Err(r) => Err(r),
                Ok(dt) => Ok(
                    DStmt::Assign(
                        n,
                        DExpr::Bin(
                            if up {
                                BinOp::Add
                            } else {
                                BinOp::Sub
                            },
                            Box::new(DExpr::Var(n)),
                            Box::new(DExpr::Conv(dt, Box::new(DExpr::Lit(1)))),
                        ),
                    ),
                ),
            }
        },
        Stmt::While(c, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, env) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, env) {
                Err(r) => Err(r),
                Ok(dec) => match spec_code(c, l) {
                    Err(r) => Err(r),
                    Ok(dc) => match spec_stmts(*body, all, env, ps) {
                        Err(r) => Err(r),
                        Ok(db) => Ok(DStmt::While(dc, inv, dec, Box::new(db))),
                    },
                },
            },
        },
        Stmt::For(init, c, step, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, spec_scope(*init, env)) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, spec_scope(*init, env)) {
                Err(r) => Err(r),
                Ok(dec) => match spec_stmt(*init, all, env, ps) {
                    Err(r) => Err(r),
                    Ok(di) => match spec_code(c, l) {
                        Err(r) => Err(r),
                        Ok(dc) => match spec_stmt(*step, all, spec_scope(*init, env), ps) {
                            Err(r) => Err(r),
                            Ok(ds) => match spec_stmts(*body, all, spec_scope(*init, env), ps) {
                                Err(r) => Err(r),
                                Ok(db) => Ok(DStmt::For(Box::new(di), dc, inv, dec, Box::new(db), Box::new(ds))),
                            },
                        },
                    },
                },
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

pub open spec fn spec_stmts(ss: Stmts, all: Fns, env: Params, ps: Params) -> Result<DStmts, Refusal>
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match spec_stmt(*s, all, env, ps) {
            Ok(d) => match spec_stmts(*rest, all, spec_scope(*s, env), ps) {
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
        Conds::Cons(k, e, l, decl, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Invariant => Err(Refusal::Misplaced(l)),
            CondKind::Decreases => Err(Refusal::Misplaced(l)),
            _ => match spec_conds(*rest, want, ps, ret) {
                Ok(dr) => if k == want {
                    match spec_contract(e, decl, ps, Some(ret), Names::Nil, l) {
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
        Stmt::While(_, _, body, _) => spec_twice_stmts(seen, *body),
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
                None => match spec_stmts(f.body, all, f.params, f.params) {
                    Err(r) => Err(r),
                    Ok(body) => Ok((req, ens, body)),
                },
            },
        },
    }
}

/// The requires lines `tail`, after one for each sequence parameter: its length fits `size_t`, decision 0064.
pub open spec fn spec_bounds(ps: Params, tail: DConds) -> DConds
    decreases ps,
{
    match ps {
        Params::Nil => tail,
        Params::Cons(n, t, rest) => match t {
            Ty::Seq(_) => DConds::Cons(
                DExpr::Bin(BinOp::Le, Box::new(DExpr::Len(Box::new(DExpr::Var(n)))), Box::new(DExpr::Lit(0xffff_ffff_ffff_ffff))),
                Box::new(spec_bounds(*rest, tail)),
            ),
            _ => spec_bounds(*rest, tail),
        },
    }
}

/// The model of a function among the functions `all` of its file, decision 0058.
pub open spec fn spec_function(f: Function, all: Fns) -> Model {
    match spec_params(f.params, f.line) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match spec_value_ty(f.ret, f.line) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match spec_inside(f, all) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, body)) => Model::Full(
                    Method { name: f.name, params: ps, ret, requires: spec_bounds(f.params, req), ensures: ens, body },
                ),
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
        Expr::Size(a) => unknown_expr(*a),
        Expr::Index(a, i) => unknown_expr(*a) || unknown_expr(*i),
        Expr::Forall(_, a) => unknown_expr(*a),
        Expr::Chain(_, _, a, b, c) => unknown_expr(*a) || unknown_expr(*b) || unknown_expr(*c),
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
        Stmt::Assign(_, e, _) => unknown_expr(e),
        Stmt::Step(_, _, _, _) => false,
        Stmt::While(c, _, body, _) => unknown_expr(c) || unknown_stmts(*body),
        Stmt::For(init, c, step, _, body, _) => unknown_stmt(*init) || unknown_expr(c) || unknown_stmt(*step) || unknown_stmts(*body),
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
        Expr::Size(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Index(a, i) => {
            if unknown_expr(*a) {
                lemma_unknown_code_is_refused(*a, line);
            } else {
                lemma_unknown_code_is_refused(*i, line);
            }
        },
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

pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns, env: Params, ps: Params)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all, env, ps).is_err(),
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
                lemma_unknown_stmts_is_refused(*t, all, env, ps);
            } else {
                lemma_unknown_stmts_is_refused(*f, all, env, ps);
            }
        },
        Stmt::Local(_, _, e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::Assign(_, e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::While(c, _, body, l) => {
            if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, env, ps);
            }
        },
        Stmt::For(init, c, step, _, body, l) => {
            if unknown_stmt(*init) {
                lemma_unknown_stmt_is_refused(*init, all, env, ps);
            } else if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else if unknown_stmt(*step) {
                lemma_unknown_stmt_is_refused(*step, all, spec_scope(*init, env), ps);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, spec_scope(*init, env), ps);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_stmts_is_refused(ss: Stmts, all: Fns, env: Params, ps: Params)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts(ss, all, env, ps).is_err(),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all, env, ps);
            } else {
                lemma_unknown_stmts_is_refused(*rest, all, spec_scope(*s, env), ps);
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
    lemma_unknown_stmts_is_refused(f.body, all, f.params, f.params);
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
        Stmt::While(_, _, body, _) => 1 + count_stmts(*body),
        Stmt::For(init, _, step, _, body, _) => 1 + count_stmt(*init) + count_stmt(*step) + count_stmts(*body),
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
        DStmt::While(_, _, _, body) => 1 + count_dstmts(*body),
        DStmt::For(init, _, _, _, body, step) => 1 + count_dstmt(*init) + count_dstmt(*step) + count_dstmts(*body),
        _ => 1,
    }
}

pub proof fn lemma_stmt_kept(s: Stmt, all: Fns, env: Params, ps: Params)
    requires
        spec_stmt(s, all, env, ps).is_ok(),
    ensures
        count_dstmt(spec_stmt(s, all, env, ps).unwrap()) == count_stmt(s),
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => {
            lemma_statements_kept(*t, all, env, ps);
            lemma_statements_kept(*f, all, env, ps);
        },
        Stmt::While(_, _, body, _) => {
            lemma_statements_kept(*body, all, env, ps);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_kept(*init, all, env, ps);
            lemma_stmt_kept(*step, all, spec_scope(*init, env), ps);
            lemma_statements_kept(*body, all, spec_scope(*init, env), ps);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches and loops included.
pub proof fn lemma_statements_kept(ss: Stmts, all: Fns, env: Params, ps: Params)
    requires
        spec_stmts(ss, all, env, ps).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, all, env, ps).unwrap()) == count_stmts(ss),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_kept(*s, all, env, ps);
            lemma_statements_kept(*rest, all, spec_scope(*s, env), ps);
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
        DStmt::AssignCall(_, k, _) => spec_callable(all, k),
        DStmt::While(_, _, _, body) => calls_resolve(*body, all),
        DStmt::For(init, _, _, _, body, step) => calls_resolve_stmt(*init, all) && calls_resolve(*body, all) && calls_resolve_stmt(*step, all),
        _ => true,
    }
}

pub proof fn lemma_stmt_calls_resolve(s: Stmt, all: Fns, env: Params, ps: Params)
    requires
        spec_stmt(s, all, env, ps).is_ok(),
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps).unwrap(), all),
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => {
            lemma_stmts_calls_resolve(*t, all, env, ps);
            lemma_stmts_calls_resolve(*f, all, env, ps);
        },
        Stmt::While(_, _, body, _) => {
            lemma_stmts_calls_resolve(*body, all, env, ps);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_calls_resolve(*init, all, env, ps);
            lemma_stmt_calls_resolve(*step, all, spec_scope(*init, env), ps);
            lemma_stmts_calls_resolve(*body, all, spec_scope(*init, env), ps);
        },
        _ => {},
    }
}

pub proof fn lemma_stmts_calls_resolve(ss: Stmts, all: Fns, env: Params, ps: Params)
    requires
        spec_stmts(ss, all, env, ps).is_ok(),
    ensures
        calls_resolve(spec_stmts(ss, all, env, ps).unwrap(), all),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all, env, ps);
            lemma_stmts_calls_resolve(*rest, all, spec_scope(*s, env), ps);
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
    lemma_stmts_calls_resolve(f.body, all, f.params, f.params);
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
        Ty::U32 => Ok(DTy::UInt32),
        Ty::U64 => Ok(DTy::UInt64),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(s) => Ok(DTy::Seq(s)),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

pub fn translate_value_ty(t: Ty, line: u32) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_value_ty(t, line),
{
    match t {
        Ty::Seq(_) => Err(Refusal::SeqParam(line)),
        _ => translate_ty(t, line),
    }
}

pub fn elem(s: Scalar) -> (r: Ty)
    ensures
        r == spec_elem(s),
{
    match s {
        Scalar::I32 => Ty::I32,
        Scalar::I64 => Ty::I64,
        Scalar::U8 => Ty::U8,
        Scalar::U32 => Ty::U32,
        Scalar::U64 => Ty::U64,
        Scalar::Bool => Ty::Bool,
    }
}

pub fn chain_ok(a: BinOp, b: BinOp) -> (r: bool)
    ensures
        r == chains(a, b),
{
    ((a == BinOp::Lt || a == BinOp::Le) && (b == BinOp::Lt || b == BinOp::Le)) || ((a == BinOp::Gt || a == BinOp::Ge) && (b
        == BinOp::Gt || b == BinOp::Ge))
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
        Expr::Lit(n, t) => match translate_ty(*t, line) {
            Ok(dt) => Ok(DExpr::Conv(dt, Box::new(DExpr::Lit(*n)))),
            Err(r) => Err(r),
        },
        Expr::Bool(b) => Ok(DExpr::Bool(*b)),
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
        Expr::Size(o) => match translate_code(o, line) {
            Ok(d) => Ok(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(d))))),
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match translate_code(o, line) {
            Ok(d) => match translate_code(i, line) {
                Ok(di) => Ok(DExpr::Index(Box::new(d), Box::new(di))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(*n, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
        _ => Err(Refusal::Syntax(line)),
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

pub fn rebind(decl: &Names, ps: &Params, name: u32) -> (r: Option<(u32, Ty)>)
    ensures
        r == spec_rebind(*decl, *ps, name),
    decreases ps,
{
    match decl {
        Names::Nil => None,
        Names::Cons(d, drest) => match ps {
            Params::Nil => None,
            Params::Cons(p, t, prest) => if *d == name {
                Some((*p, *t))
            } else {
                rebind(drest, prest, name)
            },
        },
    }
}

pub fn translate_leaf(d: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_leaf(d, t, line),
{
    match translate_ty(t, line) {
        Ok(_) => if t == Ty::I32 || t == Ty::I64 || t == Ty::U8 || t == Ty::U32 || t == Ty::U64 {
            Ok(DExpr::AsInt(Box::new(d)))
        } else {
            Ok(d)
        },
        Err(r) => Err(r),
    }
}

pub fn translate_contract(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_contract(*e, *decl, *ps, ret, *bound, line),
    decreases e,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(*n)),
        Expr::Name(n) => if has(bound, *n) {
            Ok(DExpr::Bound(*n))
        } else {
            match rebind(decl, ps, *n) {
                Some((p, t)) => translate_leaf(DExpr::Var(p), t, line),
                None => unnamed(*n, ret, line),
            }
        },
        Expr::Result => match ret {
            Some(t) => translate_leaf(DExpr::Result, t, line),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Bin(op, a, b) => match translate_contract(a, decl, ps, ret, bound, line) {
            Ok(da) => match translate_contract(b, decl, ps, ret, bound, line) {
                Ok(db) => Ok(DExpr::Bin(*op, Box::new(da), Box::new(db))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match translate_contract(a, decl, ps, ret, bound, line) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match translate_contract(a, decl, ps, ret, bound, line) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Paren(a) => translate_contract(a, decl, ps, ret, bound, line),
        Expr::Size(o) => match seq_name(o, decl, ps, ret, bound, line) {
            Ok((p, _)) => Ok(DExpr::Len(Box::new(DExpr::Var(p)))),
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match seq_name(o, decl, ps, ret, bound, line) {
            Ok((p, s)) => match translate_contract(i, decl, ps, ret, bound, line) {
                Ok(di) => translate_leaf(DExpr::Index(Box::new(DExpr::Var(p)), Box::new(di)), elem(s), line),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Forall(j, body) => {
            let inner = Names::Cons(*j, Box::new(copy_names(bound)));
            match translate_contract(body, decl, ps, ret, &inner, line) {
                Ok(db) => Ok(DExpr::Forall(*j, Box::new(db))),
                Err(r) => Err(r),
            }
        },
        Expr::Chain(o1, o2, a, b, c) => if chain_ok(*o1, *o2) {
            match translate_contract(a, decl, ps, ret, bound, line) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line) {
                    Ok(db) => match translate_contract(c, decl, ps, ret, bound, line) {
                        Ok(dc) => Ok(DExpr::Chain(*o1, *o2, Box::new(da), Box::new(db), Box::new(dc))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

pub fn has(bound: &Names, name: u32) -> (r: bool)
    ensures
        r == spec_has(*bound, name),
    decreases bound,
{
    match bound {
        Names::Nil => false,
        Names::Cons(n, rest) => *n == name || has(rest, name),
    }
}

pub fn copy_names(ns: &Names) -> (r: Names)
    ensures
        r == *ns,
    decreases ns,
{
    match ns {
        Names::Nil => Names::Nil,
        Names::Cons(n, rest) => Names::Cons(*n, Box::new(copy_names(rest))),
    }
}

pub fn unnamed(n: u32, ret: Option<Ty>, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_unnamed(n, ret, line),
{
    match ret {
        Some(_) => Err(Refusal::Name(n, line)),
        None => Err(Refusal::NoVar(n, line)),
    }
}

pub fn seq_name(o: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32) -> (r: Result<(u32, Scalar), Refusal>)
    ensures
        r == spec_seq_name(*o, *decl, *ps, ret, *bound, line),
{
    match o {
        Expr::Name(n) => if has(bound, *n) {
            Err(Refusal::Syntax(line))
        } else {
            match rebind(decl, ps, *n) {
                Some((p, Ty::Seq(s))) => Ok((p, s)),
                Some(_) => Err(Refusal::Syntax(line)),
                None => match ret {
                    Some(_) => Err(Refusal::Name(*n, line)),
                    None => Err(Refusal::NoVar(*n, line)),
                },
            }
        },
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
    translate_params(&f.params, f.line).is_ok() && translate_value_ty(f.ret, f.line).is_ok()
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

pub fn copy_params(ps: &Params) -> (r: Params)
    ensures
        r == *ps,
    decreases ps,
{
    match ps {
        Params::Nil => Params::Nil,
        Params::Cons(n, t, rest) => Params::Cons(*n, *t, Box::new(copy_params(rest))),
    }
}

pub fn scope(s: &Stmt, env: &Params) -> (r: Params)
    ensures
        r == spec_scope(*s, *env),
{
    match s {
        Stmt::Local(n, t, _, _) => Params::Cons(*n, *t, Box::new(copy_params(env))),
        _ => copy_params(env),
    }
}

pub fn names_of(ps: &Params) -> (r: Names)
    ensures
        r == spec_names_of(*ps),
    decreases ps,
{
    match ps {
        Params::Nil => Names::Nil,
        Params::Cons(n, _, rest) => Names::Cons(*n, Box::new(names_of(rest))),
    }
}

pub fn is_param(ps: &Params, name: u32) -> (r: bool)
    ensures
        r == spec_is_param(*ps, name),
    decreases ps,
{
    match ps {
        Params::Nil => false,
        Params::Cons(n, _, rest) => *n == name || is_param(rest, name),
    }
}

pub fn translate_loop_conds(cs: &Conds, want: CondKind, env: &Params) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_loop_conds(*cs, want, *env),
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, _, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Requires => Err(Refusal::Misplaced(*l)),
            CondKind::Ensures => Err(Refusal::Misplaced(*l)),
            _ => match translate_loop_conds(rest, want, env) {
                Ok(dr) => if *k == want {
                    match translate_contract(e, &names_of(env), env, None, &Names::Nil, *l) {
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

pub fn translate_stmt(s: &Stmt, all: &Fns, env: &Params, ps: &Params) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_stmt(*s, *all, *env, *ps),
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
            Ok(dc) => match translate_stmts(t, all, env, ps) {
                Ok(dt) => match translate_stmts(f, all, env, ps) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match translate_value_ty(*t, *l) {
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
        Stmt::Assign(n, e, l) => if is_param(ps, *n) {
            Err(Refusal::WriteParam(*n, *l))
        } else {
            match e {
                Expr::Call(k, nm, args, at) => match translate_call(*k, *nm, args, *at, all, *l) {
                    Ok(da) => Ok(DStmt::AssignCall(*n, *k, da)),
                    Err(r) => Err(r),
                },
                _ => match translate_code(e, *l) {
                    Ok(d) => Ok(DStmt::Assign(*n, d)),
                    Err(r) => Err(r),
                },
            }
        },
        Stmt::Step(n, t, up, l) => if is_param(ps, *n) {
            Err(Refusal::WriteParam(*n, *l))
        } else {
            match translate_ty(*t, *l) {
                Err(r) => Err(r),
                Ok(dt) => {
                    let op = if *up {
                        BinOp::Add
                    } else {
                        BinOp::Sub
                    };
                    Ok(DStmt::Assign(*n, DExpr::Bin(op, Box::new(DExpr::Var(*n)), Box::new(DExpr::Conv(dt, Box::new(DExpr::Lit(1)))))))
                },
            }
        },
        Stmt::While(c, lc, body, l) => match translate_loop_conds(lc, CondKind::Invariant, env) {
            Err(r) => Err(r),
            Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, env) {
                Err(r) => Err(r),
                Ok(dec) => match translate_code(c, *l) {
                    Err(r) => Err(r),
                    Ok(dc) => match translate_stmts(body, all, env, ps) {
                        Err(r) => Err(r),
                        Ok(db) => Ok(DStmt::While(dc, inv, dec, Box::new(db))),
                    },
                },
            },
        },
        Stmt::For(init, c, step, lc, body, l) => {
            let inner = scope(init, env);
            match translate_loop_conds(lc, CondKind::Invariant, &inner) {
                Err(r) => Err(r),
                Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, &inner) {
                    Err(r) => Err(r),
                    Ok(dec) => match translate_stmt(init, all, env, ps) {
                        Err(r) => Err(r),
                        Ok(di) => match translate_code(c, *l) {
                            Err(r) => Err(r),
                            Ok(dc) => match translate_stmt(step, all, &inner, ps) {
                                Err(r) => Err(r),
                                Ok(ds) => match translate_stmts(body, all, &inner, ps) {
                                    Err(r) => Err(r),
                                    Ok(db) => Ok(DStmt::For(Box::new(di), dc, inv, dec, Box::new(db), Box::new(ds))),
                                },
                            },
                        },
                    },
                },
            }
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_stmts(ss: &Stmts, all: &Fns, env: &Params, ps: &Params) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts(*ss, *all, *env, *ps),
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match translate_stmt(s, all, env, ps) {
            Ok(d) => match translate_stmts(rest, all, &scope(s, env), ps) {
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
        Conds::Cons(k, e, l, decl, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Invariant => Err(Refusal::Misplaced(*l)),
            CondKind::Decreases => Err(Refusal::Misplaced(*l)),
            _ => match translate_conds(rest, want, ps, ret) {
                Ok(dr) => if *k == want {
                    match translate_contract(e, decl, ps, Some(ret), &Names::Nil, *l) {
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
        Stmt::While(_, _, body, _) => twice_stmts(seen, body),
        Stmt::For(init, _, step, _, body, _) => {
            let r = twice_stmt(seen, init);
            if r.is_some() {
                r
            } else {
                let r2 = twice_stmt(seen, step);
                if r2.is_some() {
                    r2
                } else {
                    twice_stmts(seen, body)
                }
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
                None => match translate_stmts(&f.body, all, &f.params, &f.params) {
                    Err(r) => Err(r),
                    Ok(body) => Ok((req, ens, body)),
                },
            },
        },
    }
}

pub fn bounds(ps: &Params, tail: DConds) -> (r: DConds)
    ensures
        r == spec_bounds(*ps, tail),
    decreases ps,
{
    match ps {
        Params::Nil => tail,
        Params::Cons(n, t, rest) => match t {
            Ty::Seq(_) => DConds::Cons(
                DExpr::Bin(BinOp::Le, Box::new(DExpr::Len(Box::new(DExpr::Var(*n)))), Box::new(DExpr::Lit(0xffff_ffff_ffff_ffff))),
                Box::new(bounds(rest, tail)),
            ),
            _ => bounds(rest, tail),
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
        Ok(ps) => match translate_value_ty(f.ret, f.line) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match translate_inside(f, all) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, body)) => Model::Full(
                    Method { name: f.name, params: ps, ret, requires: bounds(&f.params, req), ensures: ens, body },
                ),
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
/// negation where no operand is before it. `Size` is the text `.size()`, decision 0064. `Unknown` is text with no token, by the id
/// of its kind and its line.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Tok {
    Ident(u32),
    Int(u64),
    Result,
    Op(BinOp),
    Bang,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Size,
    Forall,
    ColonColon,
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

/// The precedence of the contract language, lowest first: `==>`, which groups to the right, then `||`, `&&`, a comparison or a
/// chain of two, `+` and `-`, `*`, the prefix `!` and `-`, and the postfix `.size()` and `[e]`. Parentheses group, and `forall j ::`
/// takes all that follows, decision 0064.
/// ponytail: the parser is proved to end and to read each token once, not to follow a grammar written as a spec. Upgrade: the
/// grammar as a spec relation, and a proof that each parse is in it.
fn parse_implies(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 8usize,
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
    decreases toks.len() - pos, 7usize,
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
    decreases toks.len() - pos, 6usize,
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
    decreases toks.len() - pos, 5usize,
{
    let (a, p) = match parse_add(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if p < toks.len() {
        if let Tok::Op(op) = toks[p] {
            if is_cmp(op) {
                let (b, q) = match parse_add(toks, p + 1, line) {
                    Ok(x) => x,
                    Err(e) => return Err(e),
                };
                if q < toks.len() {
                    if let Tok::Op(op2) = toks[q] {
                        if is_cmp(op2) {
                            return match parse_add(toks, q + 1, line) {
                                Ok((c, r)) => Ok((Expr::Chain(op, op2, Box::new(a), Box::new(b), Box::new(c)), r)),
                                Err(e) => Err(e),
                            };
                        }
                    }
                }
                return Ok((Expr::Bin(op, Box::new(a), Box::new(b)), q));
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
    decreases toks.len() - pos, 4usize,
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
    decreases toks.len() - pos, 3usize,
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
    decreases toks.len() - pos, 2usize,
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
        parse_postfix(toks, pos, line)
    }
}

fn parse_postfix(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 1usize,
{
    let (mut a, mut p) = match parse_atom(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && (toks[p] == Tok::Size || toks[p] == Tok::LBracket)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        if toks[p] == Tok::Size {
            a = Expr::Size(Box::new(a));
            p = p + 1;
        } else {
            match parse_implies(toks, p + 1, line) {
                Ok((i, q)) => if q < toks.len() && toks[q] == Tok::RBracket {
                    a = Expr::Index(Box::new(a), Box::new(i));
                    p = q + 1;
                } else {
                    return Err(Refusal::Syntax(line));
                },
                Err(e) => return Err(e),
            }
        }
    }
    Ok((a, p))
}

fn parse_atom(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
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
        Tok::Forall => if toks.len() - pos > 2 && toks[pos + 2] == Tok::ColonColon {
            match toks[pos + 1] {
                Tok::Ident(j) => match parse_implies(toks, pos + 3, line) {
                    Ok((body, p)) => Ok((Expr::Forall(j, Box::new(body)), p)),
                    Err(e) => Err(e),
                },
                _ => Err(Refusal::Syntax(line)),
            }
        } else {
            Err(Refusal::Syntax(line))
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

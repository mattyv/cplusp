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

/// The element of a sequence or of an optional: a scalar type, decision 0064, or a struct of the file by its key, decision 0076.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Scalar {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Struct(u32),
}

/// The extent of a sequence: no fixed length, or a fixed length, decision 0070.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Extent {
    Dynamic,
    Fixed(u64),
}

/// A type of the subset. `Seq` is a read-only sequence of a scalar with its extent, a parameter only, decisions 0064 and 0070.
/// `Struct` is a struct of the file by its key, decision 0073. `Opt` is a `std::optional` of a scalar, decision 0075. `This` is the
/// object of a `const` member function of the struct by its key, a parameter by value, decision 0089. `ThisMut` is the object of a
/// member function that writes it, which takes it in and gives it back, decision 0096. `ThisAfter` is that object after the call,
/// as an ensures line reads it, and `Fresh` is the result of a constructor before it exists, as its requires line reads it. The
/// translator makes these two views itself. `Void` is the result type of a function that gives no value. `Other` is a type the
/// translator has no rule for, by the id of its name.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Ty {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Seq(Scalar, Extent),
    Struct(u32),
    Opt(Scalar),
    This(u32),
    ThisMut(u32),
    ThisAfter(u32),
    Fresh(u32),
    Void,
    Other(u32),
}

/// A binary operator. In code it is the machine operator of its operand type. In a contract it is the operator on the exact
/// integers.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
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
/// nothing. Both keep the value. `Integral` is a cast from one integral type to another, by both types. `Construct` is the cast the
/// compiler writes around a construction, which keeps the value of the construction, decision 0070. `Other` is a cast with no
/// rule yet, by the id of its kind.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CastKind {
    Read,
    NoOp,
    Integral(Ty, Ty),
    Construct,
    Other(u32),
}

/// An expression. In code, a name and a literal carry their type, which the compiler gave, decision 0060. A literal is never
/// negative, since a minus is an operator, so it holds the full range of `uint64_t`, decision 0063. `Bool` is `true` or `false`. In a contract, a name
/// carries no type, and the translator finds it among the parameters, and `Int` is an exact integer. `Brace` is a braced value of one scalar, such as `int64_t{a}`. `Call` is a call by the
/// key of its callee, the id of the callee's name for a refusal, its arguments and its line. `HasValue` and `Value` read an
/// optional, `Nullopt` is `std::nullopt`, and `Wrap` is a value that the compiler turns into an optional, decision 0075. `Empty`
/// is `v.empty()` and `Subspan` is `s.subspan(k)`, decision 0078. `Apply` is a call in a contract of a function of the companion
/// file, by the id of its name, decision 0079. `Suffix`, `Prefix` and `Slice` are `v[i..]`, `v[..j]` and `v[i..j]` in a contract,
/// decision 0085. `Divide` is `/` or `%` in code, with the type of its result, decision 0088. `MApply` is `o.f(args)` in a contract,
/// a call of a member function by the id of its name, decision 0090. `Old` is `old(e)` in an ensures line, decision 0096. `Cond` is
/// `c ? a : b`, decision 0098. `Unknown` is a construct with no
/// rule, by the id of its kind and its line.
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
    Copy(Box<Expr>, Ty, Ty),
    Field(Box<Expr>, u32),
    Construct(u32, Box<Args>),
    Forall(u32, Box<Expr>),
    Exists(u32, Box<Expr>),
    Chain(BinOp, BinOp, Box<Expr>, Box<Expr>, Box<Expr>),
    HasValue(Box<Expr>),
    Value(Box<Expr>),
    Nullopt,
    Wrap(Box<Expr>),
    Empty(Box<Expr>),
    Subspan(Box<Expr>, Box<Expr>),
    Apply(u32, Box<Args>),
    Suffix(Box<Expr>, Box<Expr>),
    Prefix(Box<Expr>, Box<Expr>),
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    Divide(BinOp, Box<Expr>, Box<Expr>, Ty),
    MApply(Box<Expr>, u32, Box<Args>),
    Old(Box<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    Unknown(u32, u32),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Args {
    Nil,
    Cons(Box<Expr>, Box<Args>),
}

/// A statement of the body, with its line. `Local` declares a name of a type with a start value. `Assign` writes a name. `Step`
/// adds one to a name of a type, or takes one away when its flag is false. `While` is a condition, the contract lines above the loop
/// and the body. `For` is a start, a condition, a step, the contract lines and the body, decision 0061. `SetField` writes a field of
/// the object of a member function. `Call` is a call that stands alone as a statement, by the key of its callee, the id of its
/// name and its arguments. `Exit` is `return;`, decision 0096. `Assert` is a `//@ assert` line in the body, and `Apply` is a
/// `//@ apply` line that calls a lemma of the companion file by the id of its name, decision 0099.
#[derive(PartialEq, Eq, Debug)]
pub enum Stmt {
    Return(Expr, u32),
    If(Expr, Box<Stmts>, Box<Stmts>, u32),
    Local(u32, Ty, Expr, u32),
    Assign(u32, Expr, u32),
    Step(u32, Ty, bool, u32),
    While(Expr, Box<Conds>, Box<Stmts>, u32),
    For(Box<Stmt>, Expr, Box<Stmt>, Box<Conds>, Box<Stmts>, u32),
    SetField(u32, Expr, u32),
    Call(u32, u32, Box<Args>, u32),
    Exit(u32),
    Assert(Expr, u32),
    Apply(u32, Box<Args>, u32),
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
/// other, overloads included. `line` is the line of its name. `trusted` holds when the function has the marker `CPLUSP_TRUSTED`, so
/// its contract stands with no proof and its body is not read, decision 0102.
#[derive(PartialEq, Eq, Debug)]
pub struct Function {
    pub name: u32,
    pub line: u32,
    pub params: Params,
    pub ret: Ty,
    pub trusted: bool,
    pub conds: Conds,
    pub body: Stmts,
}

/// The structs of one file: the key, the line, the fields and the member functions of each, decisions 0073 and 0090.
#[derive(PartialEq, Eq, Debug)]
pub enum Structs {
    Nil,
    Cons(u32, u32, Params, Members, Box<Structs>),
}

/// The member functions of a struct: the id of each name, the key of its function, and its return type and parameters when it is
/// pure, decisions 0090 and 0095. The unit computes which are pure from the functions themselves, `spec_mark`.
#[derive(PartialEq, Eq, Debug)]
pub enum Members {
    Nil,
    Cons(u32, u32, Option<(Ty, Params)>, Box<Members>),
}

/// The model of each struct of a file: its key and Dafny fields, or the refusal.
#[derive(PartialEq, Eq, Debug)]
pub enum StructModels {
    Nil,
    Cons(Result<(u32, DParams), Refusal>, Box<StructModels>),
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
    Struct(u32),
    Opt(Scalar),
    Void,
}

/// A Dafny expression. `AsInt` is `(e as int)`, the exact value of a machine integer. `Conv` is `(e as T)`, which Dafny proves
/// fits `T`. `IsSome` is `e.Some?`, `Get` is `e.value`, which Dafny proves holds a value, and `Nothing` and `Just` are `None` and
/// `Some(e)`. `Drop` is `s[k..]`, which Dafny proves is in range, decision 0078. `Apply` calls a function of the companion file,
/// decision 0079. `Take` is `s[..j]` and `Slice` is `s[i..j]`, decision 0085. `TDiv` and `TRem` are `trunc_div` and `trunc_rem`
/// on the exact integers. `DivIn` is `(trunc_div(a, b) as T)`, and `RemIn` is the remainder of `T`, which also needs the quotient to
/// fit `T`, decision 0088. `FCall` calls the function of a pure member function by its key, decision 0090. `After` is `this'`, the
/// object of a member function that writes it, as the body leaves it, decision 0096. `Ite` is `if c then a else b`, decision 0098.
/// A Dafny expression calls no method.
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
    Exists(u32, Box<DExpr>),
    Bound(u32),
    Chain(BinOp, BinOp, Box<DExpr>, Box<DExpr>, Box<DExpr>),
    Field(Box<DExpr>, u32),
    Ctor(u32, Box<DArgs>),
    IsSome(Box<DExpr>),
    Get(Box<DExpr>),
    Nothing,
    Just(Box<DExpr>),
    Drop(Box<DExpr>, Box<DExpr>),
    Apply(u32, Box<DArgs>),
    Take(Box<DExpr>, Box<DExpr>),
    Slice(Box<DExpr>, Box<DExpr>, Box<DExpr>),
    TDiv(Box<DExpr>, Box<DExpr>),
    TRem(Box<DExpr>, Box<DExpr>),
    DivIn(Box<DExpr>, Box<DExpr>, DTy),
    RemIn(Box<DExpr>, Box<DExpr>, DTy),
    FCall(u32, Box<DArgs>),
    After,
    Ite(Box<DExpr>, Box<DExpr>, Box<DExpr>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DArgs {
    Nil,
    Cons(DExpr, Box<DArgs>),
}

/// A Dafny statement. `Local` is `var x: T := e;`. `LocalCall` is `var x: T := m(args);`. `ReturnCall` is `result := m(args);
/// return;`, since Dafny takes no call in a `return`. `Assign` is `x := e;` and `AssignCall` is `x := m(args);`. `While` is the
/// condition, the invariants, the decreases lines and the body. `For` prints as its start, then a `while` whose body ends with the
/// step. The start and the step keep their own places, decision 0069. `SetField` is `this' := this'.(f := e);`. `Update` calls a
/// method that writes its object and writes the object back, `o := m(o, args);`, and `LocalUpdate` also sets a new local to the
/// value it gives. `CallStmt` is `m(args);` of a method that gives no value, and `Exit` is `return;`, decision 0096. `Assert` is
/// `assert e;` and `Apply` is `l(args);` of a lemma, decision 0099.
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
    For(Box<DStmt>, u32, DExpr, DConds, DConds, Box<DStmts>, Box<DStmt>, u32),
    SetField(u32, DExpr),
    Update(Obj, u32, DArgs),
    LocalUpdate(u32, DTy, Obj, u32, DArgs),
    CallStmt(u32, DArgs),
    Exit,
    Assert(DExpr),
    Apply(u32, DArgs),
}

/// The object that a call writes back: a local by its name, or the object of the member function that makes the call.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Obj {
    Local(u32),
    Object,
}

/// The statements of a Dafny body. Each keeps the place of the C++ statement it comes from, decision 0068.
#[derive(PartialEq, Eq, Debug)]
pub enum DStmts {
    Nil,
    Cons(Box<DStmt>, u32, Box<DStmts>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum DParams {
    Nil,
    Cons(u32, DTy, Box<DParams>),
}

/// Contract lines of a Dafny method or loop. Each keeps the place of the C++ contract line it comes from, decision 0068.
#[derive(PartialEq, Eq, Debug)]
pub enum DConds {
    Nil,
    Cons(DExpr, u32, Box<DConds>),
}

/// A Dafny method. `function` is the body of the Dafny function of a pure member function, decision 0090. `writes` holds when the
/// method takes its object in and gives it back as `this'`, decision 0096. `trusted` holds for the method of a trusted function: it has
/// no body, and Dafny takes its contract as given, decision 0102.
#[derive(PartialEq, Eq, Debug)]
pub struct Method {
    pub name: u32,
    pub params: DParams,
    pub ret: DTy,
    pub requires: DConds,
    pub ensures: DConds,
    pub decreases: DConds,
    pub body: DStmts,
    pub function: Option<DExpr>,
    pub writes: bool,
    pub trusted: bool,
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
/// `SeqParam` is a sequence that is no parameter. `Extent` is a sequence made from one whose length or element differs.
/// `NoField` is a field of a contract that its struct does not have. `HoldsSeq` is a local or a result of a struct that holds a
/// sequence, decision 0076. `Element` is an optional of a struct or a sequence of `bool`, which have no rule, decisions 0064 and 0076.
/// `NotPure` is a contract that calls a member function that is not pure, or no member function, by the id of the name, decision
/// 0090. `NoTarget` is a call that writes its object, on an object that is no local, by the line. `NoObject` is a field or a member
/// function in a requires line of a constructor, before the object exists, by the id of the name, decision 0096.
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
    Extent(u32),
    NoField(u32, u32),
    HoldsSeq(u32),
    Element(u32),
    NotPure(u32, u32),
    NoTarget(u32),
    NoObject(u32, u32),
}

// ------------------------------------------------------------------ the rules

/// The id of the name `operator()`. The shell gives this id to that text, decision 0098.
pub const CALL_OP: u32 = 0;

/// A type of the subset maps to its Dafny newtype, decision 0029 and the battery case signed_overflow.
pub open spec fn spec_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::I32 => Ok(DTy::Int32),
        Ty::I64 => Ok(DTy::Int64),
        Ty::U8 => Ok(DTy::UInt8),
        Ty::U32 => Ok(DTy::UInt32),
        Ty::U64 => Ok(DTy::UInt64),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        Ty::Opt(Scalar::Struct(_)) => Err(Refusal::Element(line)),
        Ty::Opt(s) => Ok(DTy::Opt(s)),
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::ThisMut(k) => Ok(DTy::Struct(k)),
        Ty::ThisAfter(k) => Ok(DTy::Struct(k)),
        Ty::Fresh(_) => Err(Refusal::Syntax(line)),
        Ty::Void => Err(Refusal::Syntax(line)),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

/// A type of a local or of a result: a type of the subset that is no sequence, decision 0064, and no struct that holds one,
/// decision 0076.
pub open spec fn spec_value_ty(t: Ty, line: u32, sd: Structs) -> Result<DTy, Refusal> {
    match spec_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => match t {
            Ty::Seq(_, _) => Err(Refusal::SeqParam(line)),
            Ty::This(_) => Err(Refusal::Syntax(line)),
            Ty::ThisMut(_) => Err(Refusal::Syntax(line)),
            Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
            Ty::Struct(k) => if spec_holds(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            _ => Ok(dt),
        },
    }
}

/// The fields of the struct `k` in the table of the file.
pub open spec fn spec_fields_of(sd: Structs, k: u32) -> Option<Params>
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, fields, _, rest) => if key == k {
            Some(fields)
        } else {
            spec_fields_of(*rest, k)
        },
    }
}

/// How deep the search for a sequence goes through structs held by value. C++ nests structs by value without a cycle, so a real
/// file stays far above it.
// ponytail: a struct nested by value deeper than this is taken to hold a sequence, and refused as a local. Upgrade: the length of
// the table as the bound.
pub const HOLD_DEPTH: u64 = 64;

/// The struct `k` holds a sequence, in a field or in a struct that a field holds by value, decision 0076.
pub open spec fn spec_holds(sd: Structs, k: u32) -> bool {
    match spec_fields_of(sd, k) {
        Some(fs) => spec_holds_any(sd, fs, HOLD_DEPTH as nat),
        None => false,
    }
}

/// A field of `ps` holds a sequence, within `depth` steps through structs held by value. At no depth left the answer is yes,
/// which refuses more and never less.
pub open spec fn spec_holds_any(sd: Structs, ps: Params, depth: nat) -> bool
    decreases depth, ps,
{
    match ps {
        Params::Nil => false,
        Params::Cons(_, t, rest) => (match t {
            Ty::Seq(_, _) => true,
            Ty::Struct(k) => depth == 0 || match spec_fields_of(sd, k) {
                Some(fs) => spec_holds_any(sd, fs, (depth - 1) as nat),
                None => false,
            },
            _ => false,
        }) || spec_holds_any(sd, *rest, depth),
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
        Scalar::Struct(k) => Ty::Struct(k),
    }
}

/// A sequence made from a sequence keeps its value when the elements are the same and the length cannot change: the new one has no
/// fixed extent, or the same extent as the old one, decision 0070. A copy of a struct keeps its value as the same struct, decision
/// 0073, and a copy of an optional as an optional of the same scalar, decision 0075.
pub open spec fn copies(from: Ty, to: Ty) -> bool {
    match (from, to) {
        (Ty::Seq(s1, e1), Ty::Seq(s2, e2)) => s1 == s2 && (e2 == Extent::Dynamic || e1 == e2),
        (Ty::Struct(a), Ty::Struct(b)) => a == b,
        (Ty::Opt(a), Ty::Opt(b)) => a == b,
        _ => false,
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
            Ok(_) => Ok(spec_code_var(v, t)),
            Err(r) => Err(r),
        },
        Expr::Bin(op, a, b) => if op == BinOp::Div || op == BinOp::Rem {
            Err(Refusal::Syntax(line))
        } else {
            match spec_code(*a, line) {
                Ok(da) => match spec_code(*b, line) {
                    Ok(db) => Ok(DExpr::Bin(op, Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        },
        Expr::Divide(op, a, b, t) => if !(op == BinOp::Div || op == BinOp::Rem) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_code(*a, line) {
                Ok(da) => match spec_code(*b, line) {
                    Ok(db) => spec_divide(op, da, db, t, line),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
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
        Expr::Copy(a, from, to) => if copies(from, to) {
            spec_code(*a, line)
        } else {
            Err(Refusal::Extent(line))
        },
        Expr::Field(o, f) => match spec_code(*o, line) {
            Ok(d) => Ok(DExpr::Field(Box::new(d), f)),
            Err(r) => Err(r),
        },
        Expr::Construct(k, args) => match spec_args(*args, line) {
            Ok(da) => Ok(DExpr::Ctor(k, Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::HasValue(o) => match spec_code(*o, line) {
            Ok(d) => Ok(DExpr::IsSome(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Value(o) => match spec_code(*o, line) {
            Ok(d) => Ok(DExpr::Get(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Nullopt => Ok(DExpr::Nothing),
        Expr::Wrap(a) => match spec_code(*a, line) {
            Ok(d) => Ok(DExpr::Just(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Empty(o) => match spec_code(*o, line) {
            Ok(d) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
            Err(r) => Err(r),
        },
        Expr::Subspan(o, k) => match spec_code(*o, line) {
            Ok(d) => match spec_code(*k, line) {
                Ok(dk) => Ok(DExpr::Drop(Box::new(d), Box::new(dk))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Cond(c, a, b) => match spec_code(*c, line) {
            Ok(dc) => match spec_code(*a, line) {
                Ok(da) => match spec_code(*b, line) {
                    Ok(db) => Ok(DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(n, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

/// A variable of code. The object of a member function that writes it is `this'` in the body, decision 0096.
pub open spec fn spec_code_var(v: u32, t: Ty) -> DExpr {
    match t {
        Ty::ThisMut(_) => DExpr::After,
        _ => DExpr::Var(v),
    }
}

/// A variable of a contract. The object after the call is `this'`, decision 0096.
pub open spec fn spec_var(v: u32, t: Ty) -> DExpr {
    match t {
        Ty::ThisAfter(_) => DExpr::After,
        _ => DExpr::Var(v),
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

/// A binary operator of a contract on the exact integers. `/` and `%` truncate as in C++, decision 0088.
pub open spec fn spec_binary(op: BinOp, da: DExpr, db: DExpr) -> DExpr {
    if op == BinOp::Div {
        DExpr::TDiv(Box::new(da), Box::new(db))
    } else if op == BinOp::Rem {
        DExpr::TRem(Box::new(da), Box::new(db))
    } else {
        DExpr::Bin(op, Box::new(da), Box::new(db))
    }
}

/// `/` or `%` of code on the integer type `t`, decision 0088. Each operand reads as an exact integer.
pub open spec fn spec_divide(op: BinOp, da: DExpr, db: DExpr, t: Ty, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !is_integer(t) {
            Err(Refusal::Convert(line))
        } else if op == BinOp::Div {
            Ok(DExpr::DivIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
        } else {
            Ok(DExpr::RemIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
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
/// parameter, and a chain is two comparisons in one direction, decision 0064. `o.has_value()` and `o.value()` read an optional on
/// a path, and the value of an integer is an exact integer, decision 0075.
pub open spec fn spec_contract(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> Result<DExpr, Refusal>
    decreases e, 1nat,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(n)),
        Expr::Bool(b) => Ok(DExpr::Bool(b)),
        Expr::Name(n) => if spec_has(bound, n) {
            Ok(DExpr::Bound(n))
        } else {
            match spec_rebind(decl, ps, n) {
                Some((p, t)) => spec_leaf(spec_var(p, t), t, line),
                None => match spec_this_field(ps, ret, n, sd) {
                    Some((d, ft)) => spec_leaf(d, ft, line),
                    None => Err(spec_no_name(n, ret, line, sd)),
                },
            }
        },
        Expr::Result => match ret {
            Some(t) => spec_leaf(DExpr::Result, t, line),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Bin(op, a, b) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line, sd) {
                Ok(db) => Ok(spec_binary(op, da, db)),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Paren(a) => spec_contract(*a, decl, ps, ret, bound, line, sd),
        Expr::Size(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Len(Box::new(d))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Empty(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match spec_path(Expr::Index(o, i), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::Suffix(o, i) => match spec_path(Expr::Suffix(o, i), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::Prefix(o, j) => match spec_path(Expr::Prefix(o, j), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::Slice(o, i, j) => match spec_path(Expr::Slice(o, i, j), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::Forall(j, body) => match spec_contract(*body, decl, ps, ret, Names::Cons(j, Box::new(bound)), line, sd) {
            Ok(db) => Ok(DExpr::Forall(j, Box::new(db))),
            Err(r) => Err(r),
        },
        Expr::Exists(j, body) => match spec_contract(*body, decl, ps, ret, Names::Cons(j, Box::new(bound)), line, sd) {
            Ok(db) => Ok(DExpr::Exists(j, Box::new(db))),
            Err(r) => Err(r),
        },
        Expr::Field(o, f) => match spec_path(Expr::Field(o, f), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::HasValue(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(_))) => Ok(DExpr::IsSome(Box::new(d))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Value(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(s))) => spec_leaf(DExpr::Get(Box::new(d)), spec_elem(s), line),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        // A bound name is an integer, so it is no function, decision 0100.
        Expr::Apply(f, args) => if spec_has(bound, f) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_functor(f, decl, ps, ret, bound, sd) {
            Some((d, k)) => match spec_member(sd, k, CALL_OP) {
                Some((key, Some((rt, mps)))) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match spec_object(ps, ret) {
            Some((o, k)) => match spec_member(sd, k, f) {
                Some((key, Some((t, mps)))) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(o, Box::new(spec_convert(da, spec_tail(mps)))))), t, line),
                    Err(r) => Err(r),
                },
                Some((_, None)) => Err(Refusal::NotPure(f, line)),
                None => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => Ok(DExpr::Apply(f, Box::new(da))),
                    Err(r) => Err(r),
                },
            },
            None => if spec_fresh_member(ret, sd, f) {
                Err(Refusal::NoObject(f, line))
            } else {
                match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => Ok(DExpr::Apply(f, Box::new(da))),
                    Err(r) => Err(r),
                }
            },
        },
        }
        },
        Expr::Old(a) => if spec_has_after(ps) {
            spec_contract(*a, decl, spec_before(ps), ret, bound, line, sd)
        } else {
            Err(Refusal::Syntax(line))
        },
        Expr::Cond(c, a, b) => match spec_contract(*c, decl, ps, ret, bound, line, sd) {
            Ok(dc) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::MApply(o, f, args) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => match spec_struct_key(t) {
                Some(k) => match spec_member(sd, k, f) {
                    Some((key, Some((rt, mps)))) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                        Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    _ => Err(Refusal::NotPure(f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Chain(o1, o2, a, b, c) => if chains(o1, o2) {
            match spec_contract(*a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => match spec_contract(*c, decl, ps, ret, bound, line, sd) {
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

/// The arguments of a call in a contract, each an expression of the contract, decision 0079.
pub open spec fn spec_contract_args(args: Args, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> Result<
    DArgs,
    Refusal,
>
    decreases args, 2nat,
{
    match args {
        Args::Nil => Ok(DArgs::Nil),
        Args::Cons(a, rest) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match spec_contract_args(*rest, decl, ps, ret, bound, line, sd) {
                Ok(dr) => Ok(DArgs::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The type of the field `f` of the struct `k` in the table of the file.
pub open spec fn spec_field_ty(sd: Structs, k: u32, f: u32) -> Option<Ty>
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, fields, _, rest) => if key == k {
            spec_lookup(fields, f)
        } else {
            spec_field_ty(*rest, k, f)
        },
    }
}

/// The type of a field name among the fields of a struct.
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

/// A path of a contract that a field reads: a parameter, `result` or a field of a path, with its Dafny form and its type, decision
/// 0073. A bound name is an integer, so it has no field.
pub open spec fn spec_path(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> Result<
    (DExpr, Ty),
    Refusal,
>
    decreases e, 0nat,
{
    match e {
        Expr::Name(n) => if spec_has(bound, n) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_rebind(decl, ps, n) {
                Some((p, t)) => Ok((spec_var(p, t), t)),
                None => match spec_this_field(ps, ret, n, sd) {
                    Some(x) => Ok(x),
                    None => Err(spec_no_name(n, ret, line, sd)),
                },
            }
        },
        Expr::Result => match ret {
            Some(t) => Ok((DExpr::Result, t)),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Paren(a) => spec_path(*a, decl, ps, ret, bound, line, sd),
        Expr::Field(o, f) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => match spec_struct_key(t) {
                Some(k) => match spec_field_ty(sd, k, f) {
                    Some(ft) => Ok((DExpr::Field(Box::new(d), f), ft)),
                    None => Err(Refusal::NoField(f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match spec_contract(*i, decl, ps, ret, bound, line, sd) {
                Ok(di) => Ok((DExpr::Index(Box::new(d), Box::new(di)), spec_elem(s))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Suffix(o, i) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match spec_contract(*i, decl, ps, ret, bound, line, sd) {
                Ok(di) => Ok((DExpr::Drop(Box::new(d), Box::new(di)), Ty::Seq(s, Extent::Dynamic))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Prefix(o, j) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match spec_contract(*j, decl, ps, ret, bound, line, sd) {
                Ok(dj) => Ok((DExpr::Take(Box::new(d), Box::new(dj)), Ty::Seq(s, Extent::Dynamic))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Slice(o, i, j) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match spec_contract(*i, decl, ps, ret, bound, line, sd) {
                Ok(di) => match spec_contract(*j, decl, ps, ret, bound, line, sd) {
                    Ok(dj) => Ok((DExpr::Slice(Box::new(d), Box::new(di), Box::new(dj)), Ty::Seq(s, Extent::Dynamic))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
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

/// The parameter `this` of a member function, with the key of its struct, decision 0089.
pub open spec fn spec_this(ps: Params) -> Option<(u32, u32)>
    decreases ps,
{
    match ps {
        Params::Nil => None,
        Params::Cons(p, t, rest) => match t {
            Ty::This(k) => Some((p, k)),
            _ => spec_this(*rest),
        },
    }
}

/// The parameter `this` of a member function, with its type: `const`, writing, or after the call. In the variables in scope in a
/// body, the locals come before it, decision 0099.
pub open spec fn spec_self(ps: Params) -> Option<(u32, Ty)>
    decreases ps,
{
    match ps {
        Params::Cons(p, t, rest) => match t {
            Ty::This(_) => Some((p, t)),
            Ty::ThisMut(_) => Some((p, t)),
            Ty::ThisAfter(_) => Some((p, t)),
            _ => spec_self(*rest),
        },
        Params::Nil => None,
    }
}

/// The function writes its object, decision 0096.
pub open spec fn spec_writes(ps: Params) -> bool {
    match spec_self(ps) {
        Some((_, Ty::ThisMut(_))) => true,
        _ => false,
    }
}

/// The parameters as an ensures line reads them: the object that the function writes is the object after the call, decision 0096.
pub open spec fn spec_after(ps: Params) -> Params
    decreases ps,
{
    match ps {
        Params::Nil => Params::Nil,
        Params::Cons(p, t, rest) => Params::Cons(
            p,
            match t {
                Ty::ThisMut(k) => Ty::ThisAfter(k),
                _ => t,
            },
            Box::new(spec_after(*rest)),
        ),
    }
}

/// The parameters as `old()` reads them: the object before the call.
pub open spec fn spec_before(ps: Params) -> Params
    decreases ps,
{
    match ps {
        Params::Nil => Params::Nil,
        Params::Cons(p, t, rest) => Params::Cons(
            p,
            match t {
                Ty::ThisAfter(k) => Ty::ThisMut(k),
                _ => t,
            },
            Box::new(spec_before(*rest)),
        ),
    }
}

/// The contract reads the object after the call, so `old()` has a meaning: an ensures line of a function that writes its object.
pub open spec fn spec_has_after(ps: Params) -> bool {
    match spec_self(ps) {
        Some((_, Ty::ThisAfter(_))) => true,
        _ => false,
    }
}

/// The object of a contract and the key of its struct: `this` of a member function, decision 0089, `this'` after a call that
/// writes it, decision 0096, or `result` of a constructor, whose result type is `This`, decision 0094.
pub open spec fn spec_object(ps: Params, ret: Option<Ty>) -> Option<(DExpr, u32)> {
    match spec_self(ps) {
        Some((p, t)) => match t {
            Ty::ThisAfter(k) => Some((DExpr::After, k)),
            Ty::This(k) => Some((DExpr::Var(p), k)),
            Ty::ThisMut(k) => Some((DExpr::Var(p), k)),
            _ => None,
        },
        None => match ret {
            Some(Ty::This(k)) => Some((DExpr::Result, k)),
            _ => None,
        },
    }
}

/// A name of a contract that is a parameter or a field of the object, of a struct type: an object whose `operator()` a call of the
/// name calls, with its Dafny form and the key of its struct, decision 0098.
pub open spec fn spec_functor(f: u32, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, sd: Structs) -> Option<(DExpr, u32)> {
    if spec_has(bound, f) {
        None
    } else {
        match spec_rebind(decl, ps, f) {
            Some((p, t)) => match spec_struct_key(t) {
                Some(k) => Some((spec_var(p, t), k)),
                None => None,
            },
            None => match spec_this_field(ps, ret, f, sd) {
                Some((d, ft)) => match spec_struct_key(ft) {
                    Some(k) => Some((d, k)),
                    None => None,
                },
                None => None,
            },
        }
    }
}

/// A requires line of a constructor reads its result before it exists. The name `n` is a member of that struct.
pub open spec fn spec_fresh_member(ret: Option<Ty>, sd: Structs, n: u32) -> bool {
    match ret {
        Some(Ty::Fresh(k)) => spec_member(sd, k, n).is_some(),
        _ => false,
    }
}

/// The view of the result type that a contract line of the kind `k` reads: a requires or a decreases line of a constructor reads
/// no object yet, decision 0096.
pub open spec fn spec_view_ret(ret: Ty, k: CondKind) -> Ty {
    match ret {
        Ty::This(s) => if k == CondKind::Ensures {
            ret
        } else {
            Ty::Fresh(s)
        },
        _ => ret,
    }
}

/// The view of the parameters that a contract line of the kind `k` reads.
pub open spec fn spec_view_ps(ps: Params, k: CondKind) -> Params {
    if k == CondKind::Ensures {
        spec_after(ps)
    } else {
        ps
    }
}

/// A name that is no parameter and is a field of the struct of the object: that field of the object, decisions 0089 and 0094.
pub open spec fn spec_this_field(ps: Params, ret: Option<Ty>, n: u32, sd: Structs) -> Option<(DExpr, Ty)> {
    match spec_object(ps, ret) {
        Some((d, k)) => match spec_field_ty(sd, k, n) {
            Some(ft) => Some((DExpr::Field(Box::new(d), n), ft)),
            None => None,
        },
        None => None,
    }
}

/// The type of the result of a function: a value type, `This` of a constructor, which must not hold a sequence, decision 0094, or
/// `void`, decision 0096.
pub open spec fn spec_ret_ty(t: Ty, line: u32, sd: Structs) -> Result<DTy, Refusal> {
    match t {
        Ty::This(k) => if spec_holds(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            Ok(DTy::Struct(k))
        },
        Ty::Void => Ok(DTy::Void),
        _ => spec_value_ty(t, line, sd),
    }
}

/// A name that is no parameter: of the contract of a function, no variable of a loop contract, or a field of a constructor's
/// result before it exists.
pub open spec fn spec_no_name(n: u32, ret: Option<Ty>, line: u32, sd: Structs) -> Refusal {
    match ret {
        Some(Ty::Fresh(k)) => if spec_field_ty(sd, k, n).is_some() {
            Refusal::NoObject(n, line)
        } else {
            Refusal::Name(n, line)
        },
        Some(_) => Refusal::Name(n, line),
        None => Refusal::NoVar(n, line),
    }
}

/// The type of a parameter. The object after a call is a view of the contract, never a parameter.
pub open spec fn spec_param_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
        _ => spec_ty(t, line),
    }
}

/// The parameters as Dafny parameters.
pub open spec fn spec_params(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match spec_param_ty(t, line) {
            Ok(dt) => match spec_params(*rest, line) {
                Ok(dr) => Ok(DParams::Cons(n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// A function has a method when its parameters and its return type are in the subset.
pub open spec fn has_signature(f: Function, sd: Structs) -> bool {
    spec_params(f.params, f.line).is_ok() && spec_ret_ty(f.ret, f.line, sd).is_ok()
}

/// A key names a function of the file that has a method.
pub open spec fn spec_callable(fs: Fns, key: u32, sd: Structs) -> bool
    decreases fs,
{
    match fs {
        Fns::Nil => false,
        Fns::Cons(f, rest) => (f.name == key && has_signature(*f, sd)) || spec_callable(*rest, key, sd),
    }
}

/// A call that stands alone, decision 0058: its callee has a method, and its arguments translate. `line` is the line of the
/// statement, and `at` is the line of the call.
pub open spec fn spec_call(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs) -> Result<DArgs, Refusal> {
    if spec_callable(all, key, sd) {
        spec_args(args, line)
    } else {
        Err(Refusal::Callee(name, at))
    }
}

/// The place of a statement, decision 0068.
pub open spec fn spec_place(s: Stmt) -> u32 {
    match s {
        Stmt::Return(_, l) => l,
        Stmt::If(_, _, _, l) => l,
        Stmt::Local(_, _, _, l) => l,
        Stmt::Assign(_, _, l) => l,
        Stmt::Step(_, _, _, l) => l,
        Stmt::While(_, _, _, l) => l,
        Stmt::For(_, _, _, _, _, l) => l,
        Stmt::SetField(_, _, l) => l,
        Stmt::Call(_, _, _, l) => l,
        Stmt::Exit(l) => l,
        Stmt::Assert(_, l) => l,
        Stmt::Apply(_, _, l) => l,
        Stmt::Unknown(_, l) => l,
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
/// at the loop, and the object as the body leaves it, decision 0099. It has no
/// `result`. A `requires` or an `ensures` line has no place above a loop.
pub open spec fn spec_loop_conds(cs: Conds, want: CondKind, env: Params, sd: Structs) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, _, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Requires => Err(Refusal::Misplaced(l)),
            CondKind::Ensures => Err(Refusal::Misplaced(l)),
            _ => match spec_loop_conds(*rest, want, env, sd) {
                Ok(dr) => if k == want {
                    match spec_contract(e, spec_names_of(env), spec_after(env), None, Names::Nil, l, sd) {
                        Ok(d) => Ok(DConds::Cons(d, l, Box::new(dr))),
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

/// The callee with the key `key` writes its object, decision 0096.
pub open spec fn spec_callee_writes(all: Fns, key: u32) -> bool {
    match spec_find(all, key) {
        Some(f) => spec_writes(f.params),
        None => false,
    }
}

/// The object of a call that writes it, decision 0096: a local, or the object of a member function that writes it. A parameter is
/// never written, and any other object has no rule yet.
pub open spec fn spec_target(o: Expr, ps: Params, line: u32) -> Result<Obj, Refusal>
    decreases o,
{
    match o {
        Expr::Var(v, t) => match t {
            Ty::ThisMut(_) => if spec_writes(ps) {
                Ok(Obj::Object)
            } else {
                Err(Refusal::Syntax(line))
            },
            _ => if spec_is_param(ps, v) {
                Err(Refusal::WriteParam(v, line))
            } else {
                Ok(Obj::Local(v))
            },
        },
        Expr::Cast(c, a) => if c == CastKind::Read || c == CastKind::NoOp {
            spec_target(*a, ps, line)
        } else {
            Err(Refusal::NoTarget(line))
        },
        Expr::Paren(a) => spec_target(*a, ps, line),
        _ => Err(Refusal::NoTarget(line)),
    }
}

/// A call that stands alone as a statement, decision 0096. A call of a function that writes its object writes the object back. A
/// call of any other function must give no value.
pub open spec fn spec_call_stmt(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    if spec_callee_writes(all, key) {
        match args {
            Args::Cons(o, rest) => match spec_target(*o, ps, line) {
                Ok(obj) => match spec_call(key, name, *rest, line, all, line, sd) {
                    Ok(da) => Ok(DStmt::Update(obj, key, da)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Args::Nil => Err(Refusal::Syntax(line)),
        }
    } else {
        match spec_call(key, name, args, line, all, line, sd) {
            Ok(da) => if spec_callee_void(all, key) {
                Ok(DStmt::CallStmt(key, da))
            } else {
                Err(Refusal::Place(line))
            },
            Err(r) => Err(r),
        }
    }
}

/// The callee with the key `key` gives no value.
pub open spec fn spec_callee_void(all: Fns, key: u32) -> bool {
    match spec_find(all, key) {
        Some(f) => f.ret == Ty::Void,
        None => false,
    }
}

/// A local whose start value is a call. A call of a function that writes its object also writes the object back, decision 0096.
pub open spec fn spec_local_call(n: u32, dt: DTy, key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, ps: Params, sd: Structs) -> Result<
    DStmt,
    Refusal,
> {
    if spec_callee_writes(all, key) {
        match args {
            Args::Cons(o, rest) => match spec_target(*o, ps, line) {
                Ok(obj) => match spec_call(key, name, *rest, at, all, line, sd) {
                    Ok(da) => Ok(DStmt::LocalUpdate(n, dt, obj, key, da)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Args::Nil => Err(Refusal::Syntax(line)),
        }
    } else {
        match spec_call(key, name, args, at, all, line, sd) {
            Ok(da) => Ok(DStmt::LocalCall(n, dt, key, da)),
            Err(r) => Err(r),
        }
    }
}

/// A statement of the body, and a list of them. `env` is the variables in scope, and `ps` the parameters. A call is in a
/// statement only as the full value of a `return`, of a local or of a write, or alone. A write is to a local, never to a
/// parameter, or to a field of the object of a member function that writes it, decision 0096.
// ponytail: `return o.f();` and `x = o.f();` of a function that writes its object are refused as a call out of place. Upgrade: an
// update to a fresh local, then the return or the write.
// ponytail: `return (f(x));` is refused as a call inside an expression. Upgrade: look through parentheses.
pub open spec fn spec_stmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e, l) => match e {
            Expr::Call(k, n, args, at) => if spec_callee_writes(all, k) {
                Err(Refusal::Place(at))
            } else {
                match spec_call(k, n, *args, at, all, l, sd) {
                    Ok(da) => Ok(DStmt::ReturnCall(k, da)),
                    Err(r) => Err(r),
                }
            },
            _ => match spec_code(e, l) {
                Ok(d) => Ok(DStmt::Return(d)),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match spec_code(c, l) {
            Ok(dc) => match spec_stmts(*t, all, env, ps, sd) {
                Ok(dt) => match spec_stmts(*f, all, env, ps, sd) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match spec_value_ty(t, l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => spec_local_call(n, dt, k, nm, *args, at, all, l, ps, sd),
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
                Expr::Call(k, nm, args, at) => if spec_callee_writes(all, k) {
                    Err(Refusal::Place(at))
                } else {
                    match spec_call(k, nm, *args, at, all, l, sd) {
                        Ok(da) => Ok(DStmt::AssignCall(n, k, da)),
                        Err(r) => Err(r),
                    }
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
        Stmt::While(c, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, env, sd) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, env, sd) {
                Err(r) => Err(r),
                Ok(dec) => match spec_code(c, l) {
                    Err(r) => Err(r),
                    Ok(dc) => match spec_stmts(*body, all, env, ps, sd) {
                        Err(r) => Err(r),
                        Ok(db) => Ok(DStmt::While(dc, inv, dec, Box::new(db))),
                    },
                },
            },
        },
        Stmt::For(init, c, step, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, spec_scope(*init, env), sd) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, spec_scope(*init, env), sd) {
                Err(r) => Err(r),
                Ok(dec) => match spec_stmt(*init, all, env, ps, sd) {
                    Err(r) => Err(r),
                    Ok(di) => match spec_code(c, l) {
                        Err(r) => Err(r),
                        Ok(dc) => match spec_stmt(*step, all, spec_scope(*init, env), ps, sd) {
                            Err(r) => Err(r),
                            Ok(ds) => match spec_stmts(*body, all, spec_scope(*init, env), ps, sd) {
                                Err(r) => Err(r),
                                Ok(db) => Ok(DStmt::For(Box::new(di), spec_place(*init), dc, inv, dec, Box::new(db), Box::new(ds), spec_place(*step))),
                            },
                        },
                    },
                },
            },
        },
        Stmt::SetField(f, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                    Some(_) => match spec_code(e, l) {
                        Ok(d) => Ok(DStmt::SetField(f, d)),
                        Err(r) => Err(r),
                    },
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::Call(k, nm, args, l) => spec_call_stmt(k, nm, *args, l, all, ps, sd),
        Stmt::Exit(_) => Ok(DStmt::Exit),
        Stmt::Assert(e, l) => match spec_contract(e, spec_names_of(env), spec_after(env), None, Names::Nil, l, sd) {
            Ok(d) => Ok(DStmt::Assert(d)),
            Err(r) => Err(r),
        },
        Stmt::Apply(f, args, l) => match spec_contract_args(*args, spec_names_of(env), spec_after(env), None, Names::Nil, l, sd) {
            Ok(da) => Ok(DStmt::Apply(f, da)),
            Err(r) => Err(r),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

pub open spec fn spec_stmts(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match spec_stmt(*s, all, env, ps, sd) {
            Ok(d) => match spec_stmts(*rest, all, spec_scope(*s, env), ps, sd) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), spec_place(*s), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// An expression names `result`.
pub open spec fn spec_has_result(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Result => true,
        Expr::Bin(_, a, b) => spec_has_result(*a) || spec_has_result(*b),
        Expr::Not(a) => spec_has_result(*a),
        Expr::Neg(a) => spec_has_result(*a),
        Expr::Paren(a) => spec_has_result(*a),
        Expr::Size(a) => spec_has_result(*a),
        Expr::Empty(a) => spec_has_result(*a),
        Expr::Apply(_, args) => spec_has_result_args(*args),
        Expr::MApply(o, _, args) => spec_has_result(*o) || spec_has_result_args(*args),
        Expr::Index(a, i) => spec_has_result(*a) || spec_has_result(*i),
        Expr::Suffix(a, i) => spec_has_result(*a) || spec_has_result(*i),
        Expr::Prefix(a, j) => spec_has_result(*a) || spec_has_result(*j),
        Expr::Slice(a, i, j) => spec_has_result(*a) || spec_has_result(*i) || spec_has_result(*j),
        Expr::Forall(_, a) => spec_has_result(*a),
        Expr::Exists(_, a) => spec_has_result(*a),
        Expr::Field(a, _) => spec_has_result(*a),
        Expr::HasValue(a) => spec_has_result(*a),
        Expr::Value(a) => spec_has_result(*a),
        Expr::Chain(_, _, a, b, c) => spec_has_result(*a) || spec_has_result(*b) || spec_has_result(*c),
        Expr::Old(a) => spec_has_result(*a),
        Expr::Cond(c, a, b) => spec_has_result(*c) || spec_has_result(*a) || spec_has_result(*b),
        _ => false,
    }
}

pub open spec fn spec_has_result_args(args: Args) -> bool
    decreases args,
{
    match args {
        Args::Nil => false,
        Args::Cons(a, rest) => spec_has_result(*a) || spec_has_result_args(*rest),
    }
}

/// The lines of one kind of the contract of a function, in their order. A word with no rule, or a line the shell could not read,
/// is refused. A `decreases` line is the measure of a recursion, and it names no `result`, decision 0072. Each kind reads its view
/// of the object, decision 0096.
pub open spec fn spec_conds(cs: Conds, want: CondKind, ps: Params, ret: Ty, sd: Structs) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, decl, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Invariant => Err(Refusal::Misplaced(l)),
            _ => match spec_conds(*rest, want, ps, ret, sd) {
                Ok(dr) => if k == want && k == CondKind::Decreases && spec_has_result(e) {
                    Err(Refusal::Syntax(l))
                } else if k == want {
                    match spec_contract(e, decl, spec_view_ps(ps, k), Some(spec_view_ret(ret, k)), Names::Nil, l, sd) {
                        Ok(d) => Ok(DConds::Cons(d, l, Box::new(dr))),
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

/// The first `return` that does not fit the result type: `return;` in a function that gives a value, or a `return` of a value in a
/// `void` function, decision 0096.
pub open spec fn spec_misreturn(ss: Stmts, void: bool) -> Option<u32>
    decreases ss,
{
    match ss {
        Stmts::Nil => None,
        Stmts::Cons(s, rest) => match spec_misreturn_stmt(*s, void) {
            Some(l) => Some(l),
            None => spec_misreturn(*rest, void),
        },
    }
}

pub open spec fn spec_misreturn_stmt(s: Stmt, void: bool) -> Option<u32>
    decreases s,
{
    match s {
        Stmt::Exit(l) => if void {
            None
        } else {
            Some(l)
        },
        Stmt::Return(_, l) => if void {
            Some(l)
        } else {
            None
        },
        Stmt::If(_, t, f, _) => match spec_misreturn(*t, void) {
            Some(l) => Some(l),
            None => spec_misreturn(*f, void),
        },
        Stmt::While(_, _, body, _) => spec_misreturn(*body, void),
        Stmt::For(init, _, step, _, body, _) => match spec_misreturn_stmt(*init, void) {
            Some(l) => Some(l),
            None => match spec_misreturn_stmt(*step, void) {
                Some(l) => Some(l),
                None => spec_misreturn(*body, void),
            },
        },
        _ => None,
    }
}

/// The contract and the body of a function whose signature is in the subset: the requires lines, the ensures lines, the decreases
/// lines and the body. A trusted function has no body, decision 0102.
pub open spec fn spec_inside(f: Function, all: Fns, sd: Structs) -> Result<(DConds, DConds, DConds, DStmts), Refusal> {
    match spec_conds(f.conds, CondKind::Requires, f.params, f.ret, sd) {
        Err(r) => Err(r),
        Ok(req) => match spec_conds(f.conds, CondKind::Ensures, f.params, f.ret, sd) {
            Err(r) => Err(r),
            Ok(ens) => match spec_conds(f.conds, CondKind::Decreases, f.params, f.ret, sd) {
                Err(r) => Err(r),
                Ok(dec) => if f.trusted {
                    Ok((req, ens, dec, DStmts::Nil))
                } else {
                    match spec_twice(f) {
                    Some((n, l)) => Err(Refusal::Twice(n, l)),
                    None => match spec_misreturn(f.body, f.ret == Ty::Void) {
                        Some(l) => Err(Refusal::Syntax(l)),
                        None => match spec_stmts(f.body, all, f.params, f.params, sd) {
                            Err(r) => Err(r),
                            Ok(body) => Ok((req, ens, dec, body)),
                        },
                    },
                    }
                },
            },
        },
    }
}

/// The requires lines `tail`, after one for each sequence parameter of fixed extent: its length is the extent, decision 0070. The
/// type `Vec` holds the bound on any other length, decision 0076.
pub open spec fn spec_bounds(ps: Params, line: u32, tail: DConds) -> DConds
    decreases ps,
{
    match ps {
        Params::Nil => tail,
        Params::Cons(n, t, rest) => match t {
            Ty::Seq(_, Extent::Fixed(k)) => DConds::Cons(
                DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(n)))), Box::new(DExpr::Lit(k))),
                line,
                Box::new(spec_bounds(*rest, line, tail)),
            ),
            _ => spec_bounds(*rest, line, tail),
        },
    }
}

/// The body of the Dafny function of a member function: the expression of its one `return`, when the function has `this` and its
/// body is that `return` alone, decision 0090. A `return` of a call is a `ReturnCall`, so a pure body holds no call.
pub open spec fn spec_pure_body(ps: Params, body: DStmts) -> Option<DExpr> {
    match spec_this(ps) {
        Some(_) => match body {
            DStmts::Cons(s, _, rest) => if *rest == DStmts::Nil {
                match *s {
                    DStmt::Return(d) => Some(d),
                    _ => None,
                }
            } else {
                None
            },
            DStmts::Nil => None,
        },
        None => None,
    }
}

/// The parameters as arguments, each by its name.
pub open spec fn spec_param_args(ps: Params) -> DArgs
    decreases ps,
{
    match ps {
        Params::Nil => DArgs::Nil,
        Params::Cons(p, _, rest) => DArgs::Cons(DExpr::Var(p), Box::new(spec_param_args(*rest))),
    }
}

/// The lines `a`, then the lines `b`.
pub open spec fn spec_append(a: DConds, b: DConds) -> DConds
    decreases a,
{
    match a {
        DConds::Nil => b,
        DConds::Cons(e, l, rest) => DConds::Cons(e, l, Box::new(spec_append(*rest, b))),
    }
}

/// The ensures lines of a method, and for a pure member function one more: `result == F(params)`, at the line of the function.
pub open spec fn spec_linked(f: Function, ens: DConds, pure: Option<DExpr>) -> DConds {
    match pure {
        Some(_) => spec_append(
            ens,
            DConds::Cons(
                DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(spec_param_args(f.params))))),
                f.line,
                Box::new(DConds::Nil),
            ),
        ),
        None => ens,
    }
}

/// The member `name` of the struct `k`: the key of its function, and its return type when it is pure.
pub open spec fn spec_member(sd: Structs, k: u32, name: u32) -> Option<(u32, Option<(Ty, Params)>)>
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, _, ms, rest) => if key == k {
            spec_member_of(ms, name)
        } else {
            spec_member(*rest, k, name)
        },
    }
}

pub open spec fn spec_member_of(ms: Members, name: u32) -> Option<(u32, Option<(Ty, Params)>)>
    decreases ms,
{
    match ms {
        Members::Nil => None,
        Members::Cons(n, key, t, rest) => if n == name {
            Some((key, t))
        } else {
            spec_member_of(*rest, name)
        },
    }
}

/// The key of the struct of a type of a path: a struct, or the object `this`.
pub open spec fn spec_struct_key(t: Ty) -> Option<u32> {
    match t {
        Ty::Struct(k) => Some(k),
        Ty::This(k) => Some(k),
        Ty::ThisMut(k) => Some(k),
        Ty::ThisAfter(k) => Some(k),
        _ => None,
    }
}

/// The function of the file with the key `key`.
pub open spec fn spec_find(fs: Fns, key: u32) -> Option<Function>
    decreases fs,
{
    match fs {
        Fns::Nil => None,
        Fns::Cons(f, rest) => if f.name == key {
            Some(*f)
        } else {
            spec_find(*rest, key)
        },
    }
}

/// The return type and parameters of the function with the key `key`, when it is a pure member function with a signature of the
/// subset. When `strict` holds, its contract must also have a model under the table `sd`, decision 0095. A trusted member is never
/// pure, decision 0102.
pub open spec fn spec_pure_ret(all: Fns, key: u32, sd: Structs, strict: bool) -> Option<(Ty, Params)> {
    match spec_find(all, key) {
        Some(f) => if !has_signature(f, sd) || f.trusted {
            None
        } else if strict {
            match spec_inside(f, all, sd) {
                Ok((_, _, _, body)) => match spec_pure_body(f.params, body) {
                    Some(_) => Some((f.ret, f.params)),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match spec_stmts(f.body, all, f.params, f.params, sd) {
                Ok(body) => match spec_pure_body(f.params, body) {
                    Some(_) => Some((f.ret, f.params)),
                    None => None,
                },
                Err(_) => None,
            }
        },
        None => None,
    }
}

pub open spec fn spec_mark_members(ms: Members, all: Fns, sd: Structs, strict: bool) -> Members
    decreases ms,
{
    match ms {
        Members::Nil => Members::Nil,
        Members::Cons(n, key, _, rest) => Members::Cons(
            n,
            key,
            spec_pure_ret(all, key, sd, strict),
            Box::new(spec_mark_members(*rest, all, sd, strict)),
        ),
    }
}

/// The table `t` with each member marked pure or not from the functions of the file, whatever the table said, decision 0090.
/// `sd` is the table that the marks read.
pub open spec fn spec_mark(t: Structs, all: Fns, sd: Structs, strict: bool) -> Structs
    decreases t,
{
    match t {
        Structs::Nil => Structs::Nil,
        Structs::Cons(k, l, fields, ms, rest) => Structs::Cons(
            k,
            l,
            fields,
            spec_mark_members(ms, all, sd, strict),
            Box::new(spec_mark(*rest, all, sd, strict)),
        ),
    }
}

/// The table of the unit: first the members whose body is pure, then of those the members whose contract also has a model under
/// that first table, decision 0095. A contract that calls a member reads the second table.
pub open spec fn spec_marked(sd: Structs, all: Fns) -> Structs {
    spec_mark(sd, all, spec_mark(sd, all, sd, false), true)
}

/// The type of Dafny of an integer type of C++.
pub open spec fn spec_int_dty(t: Ty) -> Option<DTy> {
    match t {
        Ty::I32 => Some(DTy::Int32),
        Ty::I64 => Some(DTy::Int64),
        Ty::U8 => Some(DTy::UInt8),
        Ty::U32 => Some(DTy::UInt32),
        Ty::U64 => Some(DTy::UInt64),
        _ => None,
    }
}

/// The parameters after `this`.
pub open spec fn spec_tail(ps: Params) -> Params {
    match ps {
        Params::Cons(_, _, rest) => *rest,
        Params::Nil => Params::Nil,
    }
}

/// The arguments of a contract call, each exact integer as `(e as T)` for its parameter of type `T`, decision 0095.
pub open spec fn spec_convert(da: DArgs, ps: Params) -> DArgs
    decreases da,
{
    match da {
        DArgs::Nil => DArgs::Nil,
        DArgs::Cons(d, rest) => match ps {
            Params::Cons(_, t, prest) => DArgs::Cons(
                match spec_int_dty(t) {
                    Some(dt) => DExpr::Conv(dt, Box::new(d)),
                    None => d,
                },
                Box::new(spec_convert(*rest, *prest)),
            ),
            Params::Nil => DArgs::Cons(d, Box::new(spec_convert(*rest, Params::Nil))),
        },
    }
}

/// The model of a function among the functions `all` of its file, decision 0058.
pub open spec fn spec_function(f: Function, all: Fns, sd: Structs) -> Model {
    match spec_params(f.params, f.line) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match spec_ret_ty(f.ret, f.line, sd) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match spec_inside(f, all, sd) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, dec, body)) => Model::Full(
                    Method {
                        name: f.name,
                        params: ps,
                        ret,
                        requires: spec_bounds(f.params, f.line, req),
                        ensures: spec_linked(f, ens, spec_pure_body(f.params, body)),
                        decreases: dec,
                        body,
                        function: spec_pure_body(f.params, body),
                        writes: spec_writes(f.params),
                        trusted: f.trusted,
                    },
                ),
            },
        },
    }
}

/// The model of a struct: each field a type of the subset, decision 0073. A field can be a sequence, decision 0076.
pub open spec fn spec_fields(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match spec_ty(t, line) {
            Ok(dt) => match spec_fields(*rest, line) {
                Ok(dr) => Ok(DParams::Cons(n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub open spec fn spec_structs(sd: Structs) -> StructModels
    decreases sd,
{
    match sd {
        Structs::Nil => StructModels::Nil,
        Structs::Cons(k, l, fields, _, rest) => StructModels::Cons(
            match spec_fields(fields, l) {
                Ok(df) => Ok((k, df)),
                Err(r) => Err(r),
            },
            Box::new(spec_structs(*rest)),
        ),
    }
}

/// The models of the functions `fs`, each among the functions `all` of the file.
pub open spec fn spec_unit(fs: Fns, all: Fns, sd: Structs) -> Models
    decreases fs,
{
    match fs {
        Fns::Nil => Models::Nil,
        Fns::Cons(f, rest) => Models::Cons(spec_function(*f, all, sd), Box::new(spec_unit(*rest, all, sd))),
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
        Expr::Old(a) => unknown_expr(*a),
        Expr::Cond(c, a, b) => unknown_expr(*c) || unknown_expr(*a) || unknown_expr(*b),
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
        Stmt::SetField(_, e, _) => unknown_expr(e),
        Stmt::Call(_, _, args, _) => unknown_args(*args),
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
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
        Expr::Divide(_, a, b, _) => {
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
        Expr::Copy(a, _, _) => lemma_unknown_code_is_refused(*a, line),
        Expr::Field(a, _) => lemma_unknown_code_is_refused(*a, line),
        Expr::Construct(_, args) => lemma_unknown_args_is_refused(*args, line),
        Expr::HasValue(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Value(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Wrap(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Empty(a) => lemma_unknown_code_is_refused(*a, line),
        Expr::Subspan(a, k) => {
            if unknown_expr(*a) {
                lemma_unknown_code_is_refused(*a, line);
            } else {
                lemma_unknown_code_is_refused(*k, line);
            }
        },
        Expr::Cond(c, a, b) => {
            if unknown_expr(*c) {
                lemma_unknown_code_is_refused(*c, line);
            } else if unknown_expr(*a) {
                lemma_unknown_code_is_refused(*a, line);
            } else {
                lemma_unknown_code_is_refused(*b, line);
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

pub proof fn lemma_unknown_call_is_refused(e: Expr, all: Fns, line: u32, sd: Structs)
    requires
        unknown_expr(e),
        e is Call,
    ensures
        spec_call(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_err(),
{
    if spec_callable(all, e->Call_0, sd) {
        lemma_unknown_args_is_refused(*e->Call_2, line);
    }
}

/// An object that holds a node with no rule is no target.
pub proof fn lemma_unknown_target_is_refused(o: Expr, ps: Params, line: u32)
    requires
        unknown_expr(o),
    ensures
        spec_target(o, ps, line).is_err(),
    decreases o,
{
    match o {
        Expr::Cast(c, a) => {
            if c == CastKind::Read || c == CastKind::NoOp {
                lemma_unknown_target_is_refused(*a, ps, line);
            }
        },
        Expr::Paren(a) => lemma_unknown_target_is_refused(*a, ps, line),
        _ => {},
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
    if spec_callee_writes(all, key) {
        if let Args::Cons(o, rest) = args {
            if unknown_expr(*o) {
                lemma_unknown_target_is_refused(*o, ps, line);
            } else if spec_callable(all, key, sd) {
                lemma_unknown_args_is_refused(*rest, line);
            }
        }
    } else if spec_callable(all, key, sd) {
        lemma_unknown_args_is_refused(args, line);
    }
}

pub proof fn lemma_unknown_call_stmt_is_refused(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs)
    requires
        unknown_args(args),
    ensures
        spec_call_stmt(key, name, args, line, all, ps, sd).is_err(),
{
    if spec_callee_writes(all, key) {
        if let Args::Cons(o, rest) = args {
            if unknown_expr(*o) {
                lemma_unknown_target_is_refused(*o, ps, line);
            } else if spec_callable(all, key, sd) {
                lemma_unknown_args_is_refused(*rest, line);
            }
        }
    } else if spec_callable(all, key, sd) {
        lemma_unknown_args_is_refused(args, line);
    }
}

pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all, env, ps, sd).is_err(),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l, sd);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::If(c, t, f, l) => {
            if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else if unknown_stmts(*t) {
                lemma_unknown_stmts_is_refused(*t, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*f, all, env, ps, sd);
            }
        },
        Stmt::Local(n, t, e, l) => {
            if e is Call {
                if let Ok(dt) = spec_value_ty(t, l, sd) {
                    lemma_unknown_local_call_is_refused(n, dt, e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, l, ps, sd);
                }
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::SetField(_, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::Call(k, nm, args, l) => lemma_unknown_call_stmt_is_refused(k, nm, *args, l, all, ps, sd),
        Stmt::Assign(_, e, l) => {
            if e is Call {
                lemma_unknown_call_is_refused(e, all, l, sd);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::While(c, _, body, l) => {
            if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, env, ps, sd);
            }
        },
        Stmt::For(init, c, step, _, body, l) => {
            if unknown_stmt(*init) {
                lemma_unknown_stmt_is_refused(*init, all, env, ps, sd);
            } else if unknown_expr(c) {
                lemma_unknown_code_is_refused(c, l);
            } else if unknown_stmt(*step) {
                lemma_unknown_stmt_is_refused(*step, all, spec_scope(*init, env), ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, spec_scope(*init, env), ps, sd);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_stmts_is_refused(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts(ss, all, env, ps, sd).is_err(),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*rest, all, spec_scope(*s, env), ps, sd);
            }
        },
        Stmts::Nil => {},
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
    lemma_unknown_stmts_is_refused(f.body, all, f.params, f.params, sd);
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
        DStmts::Cons(s, _, rest) => count_dstmt(*s) + count_dstmts(*rest),
    }
}

pub open spec fn count_dstmt(s: DStmt) -> nat
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => 1 + count_dstmts(*t) + count_dstmts(*f),
        DStmt::While(_, _, _, body) => 1 + count_dstmts(*body),
        DStmt::For(init, _, _, _, _, body, step, _) => 1 + count_dstmt(*init) + count_dstmt(*step) + count_dstmts(*body),
        _ => 1,
    }
}

pub proof fn lemma_stmt_kept(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == count_stmt(s),
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => {
            lemma_statements_kept(*t, all, env, ps, sd);
            lemma_statements_kept(*f, all, env, ps, sd);
        },
        Stmt::While(_, _, body, _) => {
            lemma_statements_kept(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_kept(*init, all, env, ps, sd);
            lemma_stmt_kept(*step, all, spec_scope(*init, env), ps, sd);
            lemma_statements_kept(*body, all, spec_scope(*init, env), ps, sd);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches and loops included.
pub proof fn lemma_statements_kept(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts(ss, all, env, ps, sd).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, all, env, ps, sd).unwrap()) == count_stmts(ss),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_kept(*s, all, env, ps, sd);
            lemma_statements_kept(*rest, all, spec_scope(*s, env), ps, sd);
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
pub open spec fn calls_resolve(ss: DStmts, all: Fns, sd: Structs) -> bool
    decreases ss,
{
    match ss {
        DStmts::Nil => true,
        DStmts::Cons(s, _, rest) => calls_resolve_stmt(*s, all, sd) && calls_resolve(*rest, all, sd),
    }
}

pub open spec fn calls_resolve_stmt(s: DStmt, all: Fns, sd: Structs) -> bool
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => calls_resolve(*t, all, sd) && calls_resolve(*f, all, sd),
        DStmt::LocalCall(_, _, k, _) => spec_callable(all, k, sd),
        DStmt::ReturnCall(k, _) => spec_callable(all, k, sd),
        DStmt::AssignCall(_, k, _) => spec_callable(all, k, sd),
        DStmt::Update(_, k, _) => spec_callable(all, k, sd),
        DStmt::LocalUpdate(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::CallStmt(k, _) => spec_callable(all, k, sd),
        DStmt::While(_, _, _, body) => calls_resolve(*body, all, sd),
        DStmt::For(init, _, _, _, _, body, step, _) => calls_resolve_stmt(*init, all, sd) && calls_resolve(*body, all, sd) && calls_resolve_stmt(*step, all, sd),
        _ => true,
    }
}

pub proof fn lemma_stmt_calls_resolve(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => {
            lemma_stmts_calls_resolve(*t, all, env, ps, sd);
            lemma_stmts_calls_resolve(*f, all, env, ps, sd);
        },
        Stmt::While(_, _, body, _) => {
            lemma_stmts_calls_resolve(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_calls_resolve(*init, all, env, ps, sd);
            lemma_stmt_calls_resolve(*step, all, spec_scope(*init, env), ps, sd);
            lemma_stmts_calls_resolve(*body, all, spec_scope(*init, env), ps, sd);
        },
        _ => {},
    }
}

pub proof fn lemma_stmts_calls_resolve(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts(ss, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve(spec_stmts(ss, all, env, ps, sd).unwrap(), all, sd),
    decreases ss,
{
    match ss {
        Stmts::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all, env, ps, sd);
            lemma_stmts_calls_resolve(*rest, all, spec_scope(*s, env), ps, sd);
        },
        Stmts::Nil => {},
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
        Fns::Cons(f, rest) => {
            if !(f.name == key && has_signature(*f, sd)) {
                lemma_callable_has_method(*rest, all, key, sd);
            }
        },
        Fns::Nil => {},
    }
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
        lemma_stmts_calls_resolve(f.body, all, f.params, f.params, sd);
    }
    assert forall|k: u32| spec_callable(all, k, sd) implies #[trigger] has_method(spec_unit(all, all, sd), k) by {
        lemma_callable_has_method(all, all, k, sd);
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
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        Ty::Opt(Scalar::Struct(_)) => Err(Refusal::Element(line)),
        Ty::Opt(s) => Ok(DTy::Opt(s)),
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::ThisMut(k) => Ok(DTy::Struct(k)),
        Ty::ThisAfter(k) => Ok(DTy::Struct(k)),
        Ty::Fresh(_) => Err(Refusal::Syntax(line)),
        Ty::Void => Err(Refusal::Syntax(line)),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

pub fn translate_value_ty(t: Ty, line: u32, sd: &Structs) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_value_ty(t, line, *sd),
{
    match translate_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => match t {
            Ty::Seq(_, _) => Err(Refusal::SeqParam(line)),
            Ty::This(_) => Err(Refusal::Syntax(line)),
            Ty::ThisMut(_) => Err(Refusal::Syntax(line)),
            Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
            Ty::Struct(k) => if holds_seq(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            _ => Ok(dt),
        },
    }
}

pub fn fields_of(sd: &Structs, k: u32) -> (r: Option<&Params>)
    ensures
        match r {
            Some(p) => spec_fields_of(*sd, k) == Some(*p),
            None => spec_fields_of(*sd, k) is None,
        },
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, fields, _, rest) => if *key == k {
            Some(fields)
        } else {
            fields_of(rest, k)
        },
    }
}

pub fn holds_seq(sd: &Structs, k: u32) -> (r: bool)
    ensures
        r == spec_holds(*sd, k),
{
    match fields_of(sd, k) {
        Some(fs) => holds_any(sd, fs, HOLD_DEPTH),
        None => false,
    }
}

pub fn holds_any(sd: &Structs, ps: &Params, depth: u64) -> (r: bool)
    ensures
        r == spec_holds_any(*sd, *ps, depth as nat),
    decreases depth, ps,
{
    match ps {
        Params::Nil => false,
        Params::Cons(_, t, rest) => {
            let here = match t {
                Ty::Seq(_, _) => true,
                Ty::Struct(k) => depth == 0 || match fields_of(sd, *k) {
                    Some(fs) => holds_any(sd, fs, depth - 1),
                    None => false,
                },
                _ => false,
            };
            here || holds_any(sd, rest, depth)
        },
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
        Scalar::Struct(k) => Ty::Struct(k),
    }
}

pub fn copy_ok(from: Ty, to: Ty) -> (r: bool)
    ensures
        r == copies(from, to),
{
    match (from, to) {
        (Ty::Seq(s1, e1), Ty::Seq(s2, e2)) => s1 == s2 && (e2 == Extent::Dynamic || e1 == e2),
        (Ty::Struct(a), Ty::Struct(b)) => a == b,
        (Ty::Opt(a), Ty::Opt(b)) => a == b,
        _ => false,
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
            Ok(_) => Ok(code_var(*v, *t)),
            Err(r) => Err(r),
        },
        Expr::Bin(op, a, b) => if *op == BinOp::Div || *op == BinOp::Rem {
            Err(Refusal::Syntax(line))
        } else {
            match translate_code(a, line) {
                Ok(da) => match translate_code(b, line) {
                    Ok(db) => Ok(DExpr::Bin(*op, Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        },
        Expr::Divide(op, a, b, t) => if !(*op == BinOp::Div || *op == BinOp::Rem) {
            Err(Refusal::Syntax(line))
        } else {
            match translate_code(a, line) {
                Ok(da) => match translate_code(b, line) {
                    Ok(db) => divide(*op, da, db, *t, line),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
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
        Expr::Copy(a, from, to) => if copy_ok(*from, *to) {
            translate_code(a, line)
        } else {
            Err(Refusal::Extent(line))
        },
        Expr::Field(o, f) => match translate_code(o, line) {
            Ok(d) => Ok(DExpr::Field(Box::new(d), *f)),
            Err(r) => Err(r),
        },
        Expr::Construct(k, args) => match translate_args(args, line) {
            Ok(da) => Ok(DExpr::Ctor(*k, Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::HasValue(o) => match translate_code(o, line) {
            Ok(d) => Ok(DExpr::IsSome(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Value(o) => match translate_code(o, line) {
            Ok(d) => Ok(DExpr::Get(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Nullopt => Ok(DExpr::Nothing),
        Expr::Wrap(a) => match translate_code(a, line) {
            Ok(d) => Ok(DExpr::Just(Box::new(d))),
            Err(r) => Err(r),
        },
        Expr::Empty(o) => match translate_code(o, line) {
            Ok(d) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
            Err(r) => Err(r),
        },
        Expr::Subspan(o, k) => match translate_code(o, line) {
            Ok(d) => match translate_code(k, line) {
                Ok(dk) => Ok(DExpr::Drop(Box::new(d), Box::new(dk))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Cond(c, a, b) => match translate_code(c, line) {
            Ok(dc) => match translate_code(a, line) {
                Ok(da) => match translate_code(b, line) {
                    Ok(db) => Ok(DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Name(n) => Err(Refusal::Name(*n, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

pub fn code_var(v: u32, t: Ty) -> (r: DExpr)
    ensures
        r == spec_code_var(v, t),
{
    match t {
        Ty::ThisMut(_) => DExpr::After,
        _ => DExpr::Var(v),
    }
}

pub fn contract_var(v: u32, t: Ty) -> (r: DExpr)
    ensures
        r == spec_var(v, t),
{
    match t {
        Ty::ThisAfter(_) => DExpr::After,
        _ => DExpr::Var(v),
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

pub fn binary(op: BinOp, da: DExpr, db: DExpr) -> (r: DExpr)
    ensures
        r == spec_binary(op, da, db),
{
    if op == BinOp::Div {
        DExpr::TDiv(Box::new(da), Box::new(db))
    } else if op == BinOp::Rem {
        DExpr::TRem(Box::new(da), Box::new(db))
    } else {
        DExpr::Bin(op, Box::new(da), Box::new(db))
    }
}

pub fn divide(op: BinOp, da: DExpr, db: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_divide(op, da, db, t, line),
{
    match translate_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !(t == Ty::I32 || t == Ty::I64 || t == Ty::U8 || t == Ty::U32 || t == Ty::U64) {
            Err(Refusal::Convert(line))
        } else if op == BinOp::Div {
            Ok(DExpr::DivIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
        } else {
            Ok(DExpr::RemIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
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

pub fn translate_contract(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_contract(*e, *decl, *ps, ret, *bound, line, *sd),
    decreases e, 1nat,
{
    match e {
        Expr::Int(n) => Ok(DExpr::Lit(*n)),
        Expr::Bool(b) => Ok(DExpr::Bool(*b)),
        Expr::Name(n) => if has(bound, *n) {
            Ok(DExpr::Bound(*n))
        } else {
            match rebind(decl, ps, *n) {
                Some((p, t)) => translate_leaf(contract_var(p, t), t, line),
                None => match this_field(ps, ret, *n, sd) {
                    Some((d, ft)) => translate_leaf(d, ft, line),
                    None => Err(no_name(*n, ret, line, sd)),
                },
            }
        },
        Expr::Result => match ret {
            Some(t) => translate_leaf(DExpr::Result, t, line),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Bin(op, a, b) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                Ok(db) => Ok(binary(*op, da, db)),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::Not(a) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(DExpr::Not(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Neg(a) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(DExpr::Neg(Box::new(da))),
            Err(r) => Err(r),
        },
        Expr::Paren(a) => translate_contract(a, decl, ps, ret, bound, line, sd),
        Expr::Size(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Len(Box::new(d))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Empty(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Index(_, _) | Expr::Suffix(_, _) | Expr::Prefix(_, _) | Expr::Slice(_, _, _) => match path(e, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => translate_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::Forall(j, body) => {
            let inner = Names::Cons(*j, Box::new(copy_names(bound)));
            match translate_contract(body, decl, ps, ret, &inner, line, sd) {
                Ok(db) => Ok(DExpr::Forall(*j, Box::new(db))),
                Err(r) => Err(r),
            }
        },
        Expr::Exists(j, body) => {
            let inner = Names::Cons(*j, Box::new(copy_names(bound)));
            match translate_contract(body, decl, ps, ret, &inner, line, sd) {
                Ok(db) => Ok(DExpr::Exists(*j, Box::new(db))),
                Err(r) => Err(r),
            }
        },
        Expr::Field(_, _) => match path(e, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => translate_leaf(d, t, line),
            Err(r) => Err(r),
        },
        Expr::HasValue(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(_))) => Ok(DExpr::IsSome(Box::new(d))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Value(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(s))) => translate_leaf(DExpr::Get(Box::new(d)), elem(s), line),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Apply(f, args) => if has(bound, *f) {
            Err(Refusal::Syntax(line))
        } else {
            match functor(*f, decl, ps, ret, bound, sd) {
            Some((d, k)) => match member(sd, k, CALL_OP) {
                Some((key, Some((rt, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match object(ps, ret) {
            Some((o, k)) => match member(sd, k, *f) {
                Some((key, Some((t, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(o, Box::new(convert(da, &tail(&mps)))))), t, line),
                    Err(r) => Err(r),
                },
                Some((_, None)) => Err(Refusal::NotPure(*f, line)),
                None => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => Ok(DExpr::Apply(*f, Box::new(da))),
                    Err(r) => Err(r),
                },
            },
            None => if fresh_member(ret, sd, *f) {
                Err(Refusal::NoObject(*f, line))
            } else {
                match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => Ok(DExpr::Apply(*f, Box::new(da))),
                    Err(r) => Err(r),
                }
            },
        },
        }
        },
        Expr::Old(a) => if has_after(ps) {
            translate_contract(a, decl, &before(ps), ret, bound, line, sd)
        } else {
            Err(Refusal::Syntax(line))
        },
        Expr::Cond(c, a, b) => match translate_contract(c, decl, ps, ret, bound, line, sd) {
            Ok(dc) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Expr::MApply(o, f, args) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => match struct_key(t) {
                Some(k) => match member(sd, k, *f) {
                    Some((key, Some((rt, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                        Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(DArgs::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    _ => Err(Refusal::NotPure(*f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Chain(o1, o2, a, b, c) => if chain_ok(*o1, *o2) {
            match translate_contract(a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => match translate_contract(c, decl, ps, ret, bound, line, sd) {
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

pub fn translate_contract_args(args: &Args, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: Result<
    DArgs,
    Refusal,
>)
    ensures
        r == spec_contract_args(*args, *decl, *ps, ret, *bound, line, *sd),
    decreases args, 2nat,
{
    match args {
        Args::Nil => Ok(DArgs::Nil),
        Args::Cons(a, rest) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match translate_contract_args(rest, decl, ps, ret, bound, line, sd) {
                Ok(dr) => Ok(DArgs::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn field_ty(sd: &Structs, k: u32, f: u32) -> (r: Option<Ty>)
    ensures
        r == spec_field_ty(*sd, k, f),
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, fields, _, rest) => if *key == k {
            lookup(fields, f)
        } else {
            field_ty(rest, k, f)
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

pub fn path(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: Result<(DExpr, Ty), Refusal>)
    ensures
        r == spec_path(*e, *decl, *ps, ret, *bound, line, *sd),
    decreases e, 0nat,
{
    match e {
        Expr::Name(n) => if has(bound, *n) {
            Err(Refusal::Syntax(line))
        } else {
            match rebind(decl, ps, *n) {
                Some((p, t)) => Ok((contract_var(p, t), t)),
                None => match this_field(ps, ret, *n, sd) {
                    Some(x) => Ok(x),
                    None => Err(no_name(*n, ret, line, sd)),
                },
            }
        },
        Expr::Result => match ret {
            Some(t) => Ok((DExpr::Result, t)),
            None => Err(Refusal::Syntax(line)),
        },
        Expr::Paren(a) => path(a, decl, ps, ret, bound, line, sd),
        Expr::Field(o, f) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => match struct_key(t) {
                Some(k) => match field_ty(sd, k, *f) {
                    Some(ft) => Ok((DExpr::Field(Box::new(d), *f), ft)),
                    None => Err(Refusal::NoField(*f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Index(o, i) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match translate_contract(i, decl, ps, ret, bound, line, sd) {
                Ok(di) => Ok((DExpr::Index(Box::new(d), Box::new(di)), elem(s))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Suffix(o, i) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match translate_contract(i, decl, ps, ret, bound, line, sd) {
                Ok(di) => Ok((DExpr::Drop(Box::new(d), Box::new(di)), Ty::Seq(s, Extent::Dynamic))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Prefix(o, j) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match translate_contract(j, decl, ps, ret, bound, line, sd) {
                Ok(dj) => Ok((DExpr::Take(Box::new(d), Box::new(dj)), Ty::Seq(s, Extent::Dynamic))),
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Slice(o, i, j) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => match translate_contract(i, decl, ps, ret, bound, line, sd) {
                Ok(di) => match translate_contract(j, decl, ps, ret, bound, line, sd) {
                    Ok(dj) => Ok((DExpr::Slice(Box::new(d), Box::new(di), Box::new(dj)), Ty::Seq(s, Extent::Dynamic))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        _ => Err(Refusal::Syntax(line)),
    }
}

pub fn this_param(ps: &Params) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_this(*ps),
    decreases ps,
{
    match ps {
        Params::Nil => None,
        Params::Cons(p, t, rest) => match t {
            Ty::This(k) => Some((*p, *k)),
            _ => this_param(rest),
        },
    }
}

pub fn self_param(ps: &Params) -> (r: Option<(u32, Ty)>)
    ensures
        r == spec_self(*ps),
    decreases ps,
{
    match ps {
        Params::Cons(p, t, rest) => match t {
            Ty::This(_) => Some((*p, *t)),
            Ty::ThisMut(_) => Some((*p, *t)),
            Ty::ThisAfter(_) => Some((*p, *t)),
            _ => self_param(rest),
        },
        Params::Nil => None,
    }
}

pub fn writes(ps: &Params) -> (r: bool)
    ensures
        r == spec_writes(*ps),
{
    match self_param(ps) {
        Some((_, Ty::ThisMut(_))) => true,
        _ => false,
    }
}

pub fn after(ps: &Params) -> (r: Params)
    ensures
        r == spec_after(*ps),
    decreases ps,
{
    match ps {
        Params::Nil => Params::Nil,
        Params::Cons(p, t, rest) => {
            let v = match t {
                Ty::ThisMut(k) => Ty::ThisAfter(*k),
                _ => *t,
            };
            Params::Cons(*p, v, Box::new(after(rest)))
        },
    }
}

pub fn before(ps: &Params) -> (r: Params)
    ensures
        r == spec_before(*ps),
    decreases ps,
{
    match ps {
        Params::Nil => Params::Nil,
        Params::Cons(p, t, rest) => {
            let v = match t {
                Ty::ThisAfter(k) => Ty::ThisMut(*k),
                _ => *t,
            };
            Params::Cons(*p, v, Box::new(before(rest)))
        },
    }
}

pub fn has_after(ps: &Params) -> (r: bool)
    ensures
        r == spec_has_after(*ps),
{
    match self_param(ps) {
        Some((_, Ty::ThisAfter(_))) => true,
        _ => false,
    }
}

pub fn object(ps: &Params, ret: Option<Ty>) -> (r: Option<(DExpr, u32)>)
    ensures
        r == spec_object(*ps, ret),
{
    match self_param(ps) {
        Some((p, t)) => match t {
            Ty::ThisAfter(k) => Some((DExpr::After, k)),
            Ty::This(k) => Some((DExpr::Var(p), k)),
            Ty::ThisMut(k) => Some((DExpr::Var(p), k)),
            _ => None,
        },
        None => match ret {
            Some(Ty::This(k)) => Some((DExpr::Result, k)),
            _ => None,
        },
    }
}

pub fn functor(f: u32, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, sd: &Structs) -> (r: Option<(DExpr, u32)>)
    ensures
        r == spec_functor(f, *decl, *ps, ret, *bound, *sd),
{
    if has(bound, f) {
        None
    } else {
        match rebind(decl, ps, f) {
            Some((p, t)) => match struct_key(t) {
                Some(k) => Some((contract_var(p, t), k)),
                None => None,
            },
            None => match this_field(ps, ret, f, sd) {
                Some((d, ft)) => match struct_key(ft) {
                    Some(k) => Some((d, k)),
                    None => None,
                },
                None => None,
            },
        }
    }
}

pub fn fresh_member(ret: Option<Ty>, sd: &Structs, n: u32) -> (r: bool)
    ensures
        r == spec_fresh_member(ret, *sd, n),
{
    match ret {
        Some(Ty::Fresh(k)) => member(sd, k, n).is_some(),
        _ => false,
    }
}

pub fn view_ret(ret: Ty, k: CondKind) -> (r: Ty)
    ensures
        r == spec_view_ret(ret, k),
{
    match ret {
        Ty::This(s) => if k == CondKind::Ensures {
            ret
        } else {
            Ty::Fresh(s)
        },
        _ => ret,
    }
}

pub fn view_ps(ps: &Params, k: CondKind) -> (r: Params)
    ensures
        r == spec_view_ps(*ps, k),
{
    if k == CondKind::Ensures {
        after(ps)
    } else {
        copy_params(ps)
    }
}

pub fn this_field(ps: &Params, ret: Option<Ty>, n: u32, sd: &Structs) -> (r: Option<(DExpr, Ty)>)
    ensures
        r == spec_this_field(*ps, ret, n, *sd),
{
    match object(ps, ret) {
        Some((d, k)) => match field_ty(sd, k, n) {
            Some(ft) => Some((DExpr::Field(Box::new(d), n), ft)),
            None => None,
        },
        None => None,
    }
}

pub fn ret_ty(t: Ty, line: u32, sd: &Structs) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_ret_ty(t, line, *sd),
{
    match t {
        Ty::This(k) => if holds_seq(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            Ok(DTy::Struct(k))
        },
        Ty::Void => Ok(DTy::Void),
        _ => translate_value_ty(t, line, sd),
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

pub fn no_name(n: u32, ret: Option<Ty>, line: u32, sd: &Structs) -> (r: Refusal)
    ensures
        r == spec_no_name(n, ret, line, *sd),
{
    match ret {
        Some(Ty::Fresh(k)) => if field_ty(sd, k, n).is_some() {
            Refusal::NoObject(n, line)
        } else {
            Refusal::Name(n, line)
        },
        Some(_) => Refusal::Name(n, line),
        None => Refusal::NoVar(n, line),
    }
}

pub fn param_ty(t: Ty, line: u32) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_param_ty(t, line),
{
    match t {
        Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
        _ => translate_ty(t, line),
    }
}

pub fn translate_params(ps: &Params, line: u32) -> (r: Result<DParams, Refusal>)
    ensures
        r == spec_params(*ps, line),
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match param_ty(*t, line) {
            Ok(dt) => match translate_params(rest, line) {
                Ok(dr) => Ok(DParams::Cons(*n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn signature(f: &Function, sd: &Structs) -> (r: bool)
    ensures
        r == has_signature(*f, *sd),
{
    translate_params(&f.params, f.line).is_ok() && ret_ty(f.ret, f.line, sd).is_ok()
}

pub fn callable(fs: &Fns, key: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_callable(*fs, key, *sd),
    decreases fs,
{
    match fs {
        Fns::Nil => false,
        Fns::Cons(f, rest) => (f.name == key && signature(f, sd)) || callable(rest, key, sd),
    }
}

pub fn translate_call(key: u32, name: u32, args: &Args, at: u32, all: &Fns, line: u32, sd: &Structs) -> (r: Result<DArgs, Refusal>)
    ensures
        r == spec_call(key, name, *args, at, *all, line, *sd),
{
    if callable(all, key, sd) {
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

pub fn place(s: &Stmt) -> (r: u32)
    ensures
        r == spec_place(*s),
{
    match s {
        Stmt::Return(_, l) => *l,
        Stmt::If(_, _, _, l) => *l,
        Stmt::Local(_, _, _, l) => *l,
        Stmt::Assign(_, _, l) => *l,
        Stmt::Step(_, _, _, l) => *l,
        Stmt::While(_, _, _, l) => *l,
        Stmt::For(_, _, _, _, _, l) => *l,
        Stmt::SetField(_, _, l) => *l,
        Stmt::Call(_, _, _, l) => *l,
        Stmt::Exit(l) => *l,
        Stmt::Assert(_, l) => *l,
        Stmt::Apply(_, _, l) => *l,
        Stmt::Unknown(_, l) => *l,
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

pub fn translate_loop_conds(cs: &Conds, want: CondKind, env: &Params, sd: &Structs) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_loop_conds(*cs, want, *env, *sd),
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, _, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Requires => Err(Refusal::Misplaced(*l)),
            CondKind::Ensures => Err(Refusal::Misplaced(*l)),
            _ => match translate_loop_conds(rest, want, env, sd) {
                Ok(dr) => if *k == want {
                    match translate_contract(e, &names_of(env), &after(env), None, &Names::Nil, *l, sd) {
                        Ok(d) => Ok(DConds::Cons(d, *l, Box::new(dr))),
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

pub fn callee_writes(all: &Fns, key: u32) -> (r: bool)
    ensures
        r == spec_callee_writes(*all, key),
{
    match find(all, key) {
        Some(f) => writes(&f.params),
        None => false,
    }
}

pub fn callee_void(all: &Fns, key: u32) -> (r: bool)
    ensures
        r == spec_callee_void(*all, key),
{
    match find(all, key) {
        Some(f) => f.ret == Ty::Void,
        None => false,
    }
}

pub fn target(o: &Expr, ps: &Params, line: u32) -> (r: Result<Obj, Refusal>)
    ensures
        r == spec_target(*o, *ps, line),
    decreases o,
{
    match o {
        Expr::Var(v, t) => match t {
            Ty::ThisMut(_) => if writes(ps) {
                Ok(Obj::Object)
            } else {
                Err(Refusal::Syntax(line))
            },
            _ => if is_param(ps, *v) {
                Err(Refusal::WriteParam(*v, line))
            } else {
                Ok(Obj::Local(*v))
            },
        },
        Expr::Cast(c, a) => if *c == CastKind::Read || *c == CastKind::NoOp {
            target(a, ps, line)
        } else {
            Err(Refusal::NoTarget(line))
        },
        Expr::Paren(a) => target(a, ps, line),
        _ => Err(Refusal::NoTarget(line)),
    }
}

pub fn call_stmt(key: u32, name: u32, args: &Args, line: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_call_stmt(key, name, *args, line, *all, *ps, *sd),
{
    if callee_writes(all, key) {
        match args {
            Args::Cons(o, rest) => match target(o, ps, line) {
                Ok(obj) => match translate_call(key, name, rest, line, all, line, sd) {
                    Ok(da) => Ok(DStmt::Update(obj, key, da)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Args::Nil => Err(Refusal::Syntax(line)),
        }
    } else {
        match translate_call(key, name, args, line, all, line, sd) {
            Ok(da) => if callee_void(all, key) {
                Ok(DStmt::CallStmt(key, da))
            } else {
                Err(Refusal::Place(line))
            },
            Err(r) => Err(r),
        }
    }
}

pub fn local_call(n: u32, dt: DTy, key: u32, name: u32, args: &Args, at: u32, all: &Fns, line: u32, ps: &Params, sd: &Structs) -> (r: Result<
    DStmt,
    Refusal,
>)
    ensures
        r == spec_local_call(n, dt, key, name, *args, at, *all, line, *ps, *sd),
{
    if callee_writes(all, key) {
        match args {
            Args::Cons(o, rest) => match target(o, ps, line) {
                Ok(obj) => match translate_call(key, name, rest, at, all, line, sd) {
                    Ok(da) => Ok(DStmt::LocalUpdate(n, dt, obj, key, da)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Args::Nil => Err(Refusal::Syntax(line)),
        }
    } else {
        match translate_call(key, name, args, at, all, line, sd) {
            Ok(da) => Ok(DStmt::LocalCall(n, dt, key, da)),
            Err(r) => Err(r),
        }
    }
}

pub fn translate_stmt(s: &Stmt, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_stmt(*s, *all, *env, *ps, *sd),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => match e {
            Expr::Call(k, n, args, at) => if callee_writes(all, *k) {
                Err(Refusal::Place(*at))
            } else {
                match translate_call(*k, *n, args, *at, all, *l, sd) {
                    Ok(da) => Ok(DStmt::ReturnCall(*k, da)),
                    Err(r) => Err(r),
                }
            },
            _ => match translate_code(e, *l) {
                Ok(d) => Ok(DStmt::Return(d)),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match translate_code(c, *l) {
            Ok(dc) => match translate_stmts(t, all, env, ps, sd) {
                Ok(dt) => match translate_stmts(f, all, env, ps, sd) {
                    Ok(df) => Ok(DStmt::If(dc, Box::new(dt), Box::new(df))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Local(n, t, e, l) => match translate_value_ty(*t, *l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => local_call(*n, dt, *k, *nm, args, *at, all, *l, ps, sd),
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
                Expr::Call(k, nm, args, at) => if callee_writes(all, *k) {
                    Err(Refusal::Place(*at))
                } else {
                    match translate_call(*k, *nm, args, *at, all, *l, sd) {
                        Ok(da) => Ok(DStmt::AssignCall(*n, *k, da)),
                        Err(r) => Err(r),
                    }
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
        Stmt::While(c, lc, body, l) => match translate_loop_conds(lc, CondKind::Invariant, env, sd) {
            Err(r) => Err(r),
            Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, env, sd) {
                Err(r) => Err(r),
                Ok(dec) => match translate_code(c, *l) {
                    Err(r) => Err(r),
                    Ok(dc) => match translate_stmts(body, all, env, ps, sd) {
                        Err(r) => Err(r),
                        Ok(db) => Ok(DStmt::While(dc, inv, dec, Box::new(db))),
                    },
                },
            },
        },
        Stmt::For(init, c, step, lc, body, l) => {
            let inner = scope(init, env);
            match translate_loop_conds(lc, CondKind::Invariant, &inner, sd) {
                Err(r) => Err(r),
                Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, &inner, sd) {
                    Err(r) => Err(r),
                    Ok(dec) => match translate_stmt(init, all, env, ps, sd) {
                        Err(r) => Err(r),
                        Ok(di) => match translate_code(c, *l) {
                            Err(r) => Err(r),
                            Ok(dc) => match translate_stmt(step, all, &inner, ps, sd) {
                                Err(r) => Err(r),
                                Ok(ds) => match translate_stmts(body, all, &inner, ps, sd) {
                                    Err(r) => Err(r),
                                    Ok(db) => Ok(DStmt::For(Box::new(di), place(init), dc, inv, dec, Box::new(db), Box::new(ds), place(step))),
                                },
                            },
                        },
                    },
                },
            }
        },
        Stmt::SetField(f, e, l) => match self_param(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match field_ty(sd, k, *f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(*l)),
                    Some(_) => match translate_code(e, *l) {
                        Ok(d) => Ok(DStmt::SetField(*f, d)),
                        Err(r) => Err(r),
                    },
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::WriteParam(p, *l)),
            },
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::Call(k, nm, args, l) => call_stmt(*k, *nm, args, *l, all, ps, sd),
        Stmt::Exit(_) => Ok(DStmt::Exit),
        Stmt::Assert(e, l) => match translate_contract(e, &names_of(env), &after(env), None, &Names::Nil, *l, sd) {
            Ok(d) => Ok(DStmt::Assert(d)),
            Err(r) => Err(r),
        },
        Stmt::Apply(f, args, l) => match translate_contract_args(args, &names_of(env), &after(env), None, &Names::Nil, *l, sd) {
            Ok(da) => Ok(DStmt::Apply(*f, da)),
            Err(r) => Err(r),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_stmts(ss: &Stmts, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts(*ss, *all, *env, *ps, *sd),
    decreases ss,
{
    match ss {
        Stmts::Nil => Ok(DStmts::Nil),
        Stmts::Cons(s, rest) => match translate_stmt(s, all, env, ps, sd) {
            Ok(d) => match translate_stmts(rest, all, &scope(s, env), ps, sd) {
                Ok(dr) => Ok(DStmts::Cons(Box::new(d), place(s), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn has_result(e: &Expr) -> (r: bool)
    ensures
        r == spec_has_result(*e),
    decreases e,
{
    match e {
        Expr::Result => true,
        Expr::Bin(_, a, b) => has_result(a) || has_result(b),
        Expr::Not(a) => has_result(a),
        Expr::Neg(a) => has_result(a),
        Expr::Paren(a) => has_result(a),
        Expr::Size(a) => has_result(a),
        Expr::Empty(a) => has_result(a),
        Expr::Apply(_, args) => has_result_args(args),
        Expr::MApply(o, _, args) => has_result(o) || has_result_args(args),
        Expr::Index(a, i) => has_result(a) || has_result(i),
        Expr::Suffix(a, i) => has_result(a) || has_result(i),
        Expr::Prefix(a, j) => has_result(a) || has_result(j),
        Expr::Slice(a, i, j) => has_result(a) || has_result(i) || has_result(j),
        Expr::Forall(_, a) => has_result(a),
        Expr::Exists(_, a) => has_result(a),
        Expr::Field(a, _) => has_result(a),
        Expr::HasValue(a) => has_result(a),
        Expr::Value(a) => has_result(a),
        Expr::Chain(_, _, a, b, c) => has_result(a) || has_result(b) || has_result(c),
        Expr::Old(a) => has_result(a),
        Expr::Cond(c, a, b) => has_result(c) || has_result(a) || has_result(b),
        _ => false,
    }
}

pub fn has_result_args(args: &Args) -> (r: bool)
    ensures
        r == spec_has_result_args(*args),
    decreases args,
{
    match args {
        Args::Nil => false,
        Args::Cons(a, rest) => has_result(a) || has_result_args(rest),
    }
}

pub fn translate_conds(cs: &Conds, want: CondKind, ps: &Params, ret: Ty, sd: &Structs) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_conds(*cs, want, *ps, ret, *sd),
    decreases cs,
{
    match cs {
        Conds::Nil => Ok(DConds::Nil),
        Conds::Cons(k, e, l, decl, rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Invariant => Err(Refusal::Misplaced(*l)),
            _ => match translate_conds(rest, want, ps, ret, sd) {
                Ok(dr) => if *k == want && *k == CondKind::Decreases && has_result(e) {
                    Err(Refusal::Syntax(*l))
                } else if *k == want {
                    match translate_contract(e, decl, &view_ps(ps, *k), Some(view_ret(ret, *k)), &Names::Nil, *l, sd) {
                        Ok(d) => Ok(DConds::Cons(d, *l, Box::new(dr))),
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

pub fn misreturn(ss: &Stmts, void: bool) -> (r: Option<u32>)
    ensures
        r == spec_misreturn(*ss, void),
    decreases ss,
{
    match ss {
        Stmts::Nil => None,
        Stmts::Cons(s, rest) => match misreturn_stmt(s, void) {
            Some(l) => Some(l),
            None => misreturn(rest, void),
        },
    }
}

pub fn misreturn_stmt(s: &Stmt, void: bool) -> (r: Option<u32>)
    ensures
        r == spec_misreturn_stmt(*s, void),
    decreases s,
{
    match s {
        Stmt::Exit(l) => if void {
            None
        } else {
            Some(*l)
        },
        Stmt::Return(_, l) => if void {
            Some(*l)
        } else {
            None
        },
        Stmt::If(_, t, f, _) => match misreturn(t, void) {
            Some(l) => Some(l),
            None => misreturn(f, void),
        },
        Stmt::While(_, _, body, _) => misreturn(body, void),
        Stmt::For(init, _, step, _, body, _) => match misreturn_stmt(init, void) {
            Some(l) => Some(l),
            None => match misreturn_stmt(step, void) {
                Some(l) => Some(l),
                None => misreturn(body, void),
            },
        },
        _ => None,
    }
}

pub fn translate_inside(f: &Function, all: &Fns, sd: &Structs) -> (r: Result<(DConds, DConds, DConds, DStmts), Refusal>)
    ensures
        r == spec_inside(*f, *all, *sd),
{
    match translate_conds(&f.conds, CondKind::Requires, &f.params, f.ret, sd) {
        Err(r) => Err(r),
        Ok(req) => match translate_conds(&f.conds, CondKind::Ensures, &f.params, f.ret, sd) {
            Err(r) => Err(r),
            Ok(ens) => match translate_conds(&f.conds, CondKind::Decreases, &f.params, f.ret, sd) {
                Err(r) => Err(r),
                Ok(dec) => if f.trusted {
                    Ok((req, ens, dec, DStmts::Nil))
                } else {
                    match twice(f) {
                    Some((n, l)) => Err(Refusal::Twice(n, l)),
                    None => match misreturn(&f.body, f.ret == Ty::Void) {
                        Some(l) => Err(Refusal::Syntax(l)),
                        None => match translate_stmts(&f.body, all, &f.params, &f.params, sd) {
                            Err(r) => Err(r),
                            Ok(body) => Ok((req, ens, dec, body)),
                        },
                    },
                    }
                },
            },
        },
    }
}

pub fn bounds(ps: &Params, line: u32, tail: DConds) -> (r: DConds)
    ensures
        r == spec_bounds(*ps, line, tail),
    decreases ps,
{
    match ps {
        Params::Nil => tail,
        Params::Cons(n, t, rest) => match t {
            Ty::Seq(_, Extent::Fixed(k)) => DConds::Cons(
                DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(*n)))), Box::new(DExpr::Lit(*k))),
                line,
                Box::new(bounds(rest, line, tail)),
            ),
            _ => bounds(rest, line, tail),
        },
    }
}

/// The model of one function among the functions `all` of its file.
/// An exact copy of a Dafny expression.
pub fn copy_dexpr(d: &DExpr) -> (r: DExpr)
    ensures
        r == *d,
    decreases d,
{
    match d {
        DExpr::Lit(x0) => DExpr::Lit(*x0),
        DExpr::Bool(x0) => DExpr::Bool(*x0),
        DExpr::Var(x0) => DExpr::Var(*x0),
        DExpr::Result => DExpr::Result,
        DExpr::Bin(x0, x1, x2) => DExpr::Bin(*x0, Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::Not(x0) => DExpr::Not(Box::new(copy_dexpr(x0))),
        DExpr::Neg(x0) => DExpr::Neg(Box::new(copy_dexpr(x0))),
        DExpr::AsInt(x0) => DExpr::AsInt(Box::new(copy_dexpr(x0))),
        DExpr::Conv(x0, x1) => DExpr::Conv(*x0, Box::new(copy_dexpr(x1))),
        DExpr::Len(x0) => DExpr::Len(Box::new(copy_dexpr(x0))),
        DExpr::Index(x0, x1) => DExpr::Index(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::Forall(x0, x1) => DExpr::Forall(*x0, Box::new(copy_dexpr(x1))),
        DExpr::Exists(x0, x1) => DExpr::Exists(*x0, Box::new(copy_dexpr(x1))),
        DExpr::Bound(x0) => DExpr::Bound(*x0),
        DExpr::Chain(x0, x1, x2, x3, x4) => DExpr::Chain(*x0, *x1, Box::new(copy_dexpr(x2)), Box::new(copy_dexpr(x3)), Box::new(copy_dexpr(x4))),
        DExpr::Field(x0, x1) => DExpr::Field(Box::new(copy_dexpr(x0)), *x1),
        DExpr::Ctor(x0, x1) => DExpr::Ctor(*x0, Box::new(copy_dargs(x1))),
        DExpr::IsSome(x0) => DExpr::IsSome(Box::new(copy_dexpr(x0))),
        DExpr::Get(x0) => DExpr::Get(Box::new(copy_dexpr(x0))),
        DExpr::Nothing => DExpr::Nothing,
        DExpr::Just(x0) => DExpr::Just(Box::new(copy_dexpr(x0))),
        DExpr::Drop(x0, x1) => DExpr::Drop(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::Apply(x0, x1) => DExpr::Apply(*x0, Box::new(copy_dargs(x1))),
        DExpr::Take(x0, x1) => DExpr::Take(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::Slice(x0, x1, x2) => DExpr::Slice(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::TDiv(x0, x1) => DExpr::TDiv(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::TRem(x0, x1) => DExpr::TRem(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::DivIn(x0, x1, x2) => DExpr::DivIn(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), *x2),
        DExpr::RemIn(x0, x1, x2) => DExpr::RemIn(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), *x2),
        DExpr::FCall(x0, x1) => DExpr::FCall(*x0, Box::new(copy_dargs(x1))),
        DExpr::After => DExpr::After,
        DExpr::Ite(x0, x1, x2) => DExpr::Ite(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
    }
}

pub fn copy_dargs(a: &DArgs) -> (r: DArgs)
    ensures
        r == *a,
    decreases a,
{
    match a {
        DArgs::Nil => DArgs::Nil,
        DArgs::Cons(d, rest) => DArgs::Cons(copy_dexpr(d), Box::new(copy_dargs(rest))),
    }
}

pub fn pure_body(ps: &Params, body: &DStmts) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_body(*ps, *body),
{
    match this_param(ps) {
        Some(_) => match body {
            DStmts::Cons(s, _, rest) => match &**rest {
                DStmts::Nil => match &**s {
                    DStmt::Return(d) => Some(copy_dexpr(d)),
                    _ => None,
                },
                _ => None,
            },
            DStmts::Nil => None,
        },
        None => None,
    }
}

pub fn param_args(ps: &Params) -> (r: DArgs)
    ensures
        r == spec_param_args(*ps),
    decreases ps,
{
    match ps {
        Params::Nil => DArgs::Nil,
        Params::Cons(p, _, rest) => DArgs::Cons(DExpr::Var(*p), Box::new(param_args(rest))),
    }
}

pub fn append(a: DConds, b: DConds) -> (r: DConds)
    ensures
        r == spec_append(a, b),
    decreases a,
{
    match a {
        DConds::Nil => b,
        DConds::Cons(e, l, rest) => DConds::Cons(e, l, Box::new(append(*rest, b))),
    }
}

pub fn linked(f: &Function, ens: DConds, pure: &Option<DExpr>) -> (r: DConds)
    ensures
        r == spec_linked(*f, ens, *pure),
{
    match pure {
        Some(_) => append(
            ens,
            DConds::Cons(
                DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(param_args(&f.params))))),
                f.line,
                Box::new(DConds::Nil),
            ),
        ),
        None => ens,
    }
}

pub fn member(sd: &Structs, k: u32, name: u32) -> (r: Option<(u32, Option<(Ty, Params)>)>)
    ensures
        r == spec_member(*sd, k, name),
    decreases sd,
{
    match sd {
        Structs::Nil => None,
        Structs::Cons(key, _, _, ms, rest) => if *key == k {
            member_of(ms, name)
        } else {
            member(rest, k, name)
        },
    }
}

pub fn member_of(ms: &Members, name: u32) -> (r: Option<(u32, Option<(Ty, Params)>)>)
    ensures
        r == spec_member_of(*ms, name),
    decreases ms,
{
    match ms {
        Members::Nil => None,
        Members::Cons(n, key, t, rest) => if *n == name {
            match t {
                Some((rt, mps)) => Some((*key, Some((*rt, copy_params(mps))))),
                None => Some((*key, None)),
            }
        } else {
            member_of(rest, name)
        },
    }
}

pub fn struct_key(t: Ty) -> (r: Option<u32>)
    ensures
        r == spec_struct_key(t),
{
    match t {
        Ty::Struct(k) => Some(k),
        Ty::This(k) => Some(k),
        Ty::ThisMut(k) => Some(k),
        Ty::ThisAfter(k) => Some(k),
        _ => None,
    }
}

pub fn find(fs: &Fns, key: u32) -> (r: Option<&Function>)
    ensures
        match r {
            Some(f) => spec_find(*fs, key) == Some(*f),
            None => spec_find(*fs, key) is None,
        },
    decreases fs,
{
    match fs {
        Fns::Nil => None,
        Fns::Cons(f, rest) => if f.name == key {
            Some(&**f)
        } else {
            find(rest, key)
        },
    }
}

pub fn pure_ret(all: &Fns, key: u32, sd: &Structs, strict: bool) -> (r: Option<(Ty, Params)>)
    ensures
        r == spec_pure_ret(*all, key, *sd, strict),
{
    match find(all, key) {
        Some(f) => if !signature(f, sd) || f.trusted {
            None
        } else if strict {
            match translate_inside(f, all, sd) {
                Ok((_, _, _, body)) => match pure_body(&f.params, &body) {
                    Some(_) => Some((f.ret, copy_params(&f.params))),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match translate_stmts(&f.body, all, &f.params, &f.params, sd) {
                Ok(body) => match pure_body(&f.params, &body) {
                    Some(_) => Some((f.ret, copy_params(&f.params))),
                    None => None,
                },
                Err(_) => None,
            }
        },
        None => None,
    }
}

pub fn mark_members(ms: &Members, all: &Fns, sd: &Structs, strict: bool) -> (r: Members)
    ensures
        r == spec_mark_members(*ms, *all, *sd, strict),
    decreases ms,
{
    match ms {
        Members::Nil => Members::Nil,
        Members::Cons(n, key, _, rest) => Members::Cons(*n, *key, pure_ret(all, *key, sd, strict), Box::new(mark_members(rest, all, sd, strict))),
    }
}

pub fn mark(t: &Structs, all: &Fns, sd: &Structs, strict: bool) -> (r: Structs)
    ensures
        r == spec_mark(*t, *all, *sd, strict),
    decreases t,
{
    match t {
        Structs::Nil => Structs::Nil,
        Structs::Cons(k, l, fields, ms, rest) => Structs::Cons(
            *k,
            *l,
            copy_params(fields),
            mark_members(ms, all, sd, strict),
            Box::new(mark(rest, all, sd, strict)),
        ),
    }
}

pub fn int_dty(t: Ty) -> (r: Option<DTy>)
    ensures
        r == spec_int_dty(t),
{
    match t {
        Ty::I32 => Some(DTy::Int32),
        Ty::I64 => Some(DTy::Int64),
        Ty::U8 => Some(DTy::UInt8),
        Ty::U32 => Some(DTy::UInt32),
        Ty::U64 => Some(DTy::UInt64),
        _ => None,
    }
}

pub fn tail(ps: &Params) -> (r: Params)
    ensures
        r == spec_tail(*ps),
{
    match ps {
        Params::Cons(_, _, rest) => copy_params(rest),
        Params::Nil => Params::Nil,
    }
}

pub fn convert(da: DArgs, ps: &Params) -> (r: DArgs)
    ensures
        r == spec_convert(da, *ps),
    decreases da,
{
    match da {
        DArgs::Nil => DArgs::Nil,
        DArgs::Cons(d, rest) => match ps {
            Params::Cons(_, t, prest) => DArgs::Cons(
                match int_dty(*t) {
                    Some(dt) => DExpr::Conv(dt, Box::new(d)),
                    None => d,
                },
                Box::new(convert(*rest, prest)),
            ),
            Params::Nil => DArgs::Cons(d, Box::new(convert(*rest, &Params::Nil))),
        },
    }
}

pub fn translate_function(f: &Function, all: &Fns, sd: &Structs) -> (r: Model)
    ensures
        r == spec_function(*f, *all, *sd),
{
    match translate_params(&f.params, f.line) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match ret_ty(f.ret, f.line, sd) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match translate_inside(f, all, sd) {
                Err(r) => Model::Bare(f.name, ps, ret, r),
                Ok((req, ens, dec, body)) => {
                    let pure = pure_body(&f.params, &body);
                    let ensures = linked(f, ens, &pure);
                    Model::Full(
                        Method {
                            name: f.name,
                            params: ps,
                            ret,
                            requires: bounds(&f.params, f.line, req),
                            ensures,
                            decreases: dec,
                            body,
                            function: pure,
                            writes: writes(&f.params),
                            trusted: f.trusted,
                        },
                    )
                },
            },
        },
    }
}

fn translate_each(fs: &Fns, all: &Fns, sd: &Structs) -> (r: Models)
    ensures
        r == spec_unit(*fs, *all, *sd),
    decreases fs,
{
    match fs {
        Fns::Nil => Models::Nil,
        Fns::Cons(f, rest) => Models::Cons(translate_function(f, all, sd), Box::new(translate_each(rest, all, sd))),
    }
}

fn translate_fields(ps: &Params, line: u32) -> (r: Result<DParams, Refusal>)
    ensures
        r == spec_fields(*ps, line),
    decreases ps,
{
    match ps {
        Params::Nil => Ok(DParams::Nil),
        Params::Cons(n, t, rest) => match translate_ty(*t, line) {
            Ok(dt) => match translate_fields(rest, line) {
                Ok(dr) => Ok(DParams::Cons(*n, dt, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The models of the structs of one file, in their order.
pub fn translate_structs(sd: &Structs) -> (r: StructModels)
    ensures
        r == spec_structs(*sd),
    decreases sd,
{
    match sd {
        Structs::Nil => StructModels::Nil,
        Structs::Cons(k, l, fields, _, rest) => {
            let m = match translate_fields(fields, *l) {
                Ok(df) => Ok((*k, df)),
                Err(r) => Err(r),
            };
            StructModels::Cons(m, Box::new(translate_structs(rest)))
        },
    }
}

/// The models of the functions of one file, in their order.
pub fn translate_unit(all: &Fns, sd: &Structs) -> (r: Models)
    ensures
        r == spec_unit(*all, *all, spec_marked(*sd, *all)),
{
    let first = mark(sd, all, sd, false);
    let marked = mark(sd, all, &first, true);
    translate_each(all, all, &marked)
}

// ------------------------------------------------------------------ the contract parser

/// A token of a contract line. The shell cuts the text into tokens. `Op` holds `- ` as `Sub`, and the parser reads it as a
/// negation where no operand is before it. `Size` is the text `.size()`, decision 0064. `Field` is `.name`, decision 0073.
/// `HasValue` and `Value` are the texts `.has_value()` and `.value()`, decision 0075. `Empty` is `.empty()`, decision 0078. `Comma`
/// parts the arguments of a call, decision 0079. `Bool` is `true`
/// or `false`, decision 0084. `Old` is the word `old`, decision 0096. `Question` and `Colon` are `?` and `:`, decision 0098.
/// `Unknown` is text with no token, by the id of
/// its kind and its line.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Tok {
    Ident(u32),
    Int(u64),
    Bool(bool),
    Result,
    Op(BinOp),
    Bang,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Size,
    Field(u32),
    HasValue,
    Value,
    Empty,
    Comma,
    DotDot,
    Forall,
    Exists,
    ColonColon,
    Old,
    Question,
    Colon,
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

/// The precedence of the contract language, lowest first: `==>`, which groups to the right, then `?:`, then `||`, `&&`, a comparison or a
/// chain of two, `+` and `-`, `*`, the prefix `!` and `-`, and the postfix `.size()` and `[e]`. Parentheses group, and `forall j ::`
/// takes all that follows, decision 0064.
/// ponytail: the parser is proved to end and to read each token once, not to follow a grammar written as a spec. Upgrade: the
/// grammar as a spec relation, and a proof that each parse is in it.
fn parse_implies(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 9usize,
{
    let (a, p) = match parse_cond(toks, pos, line) {
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

/// `c ? a : b`, decision 0098. The middle part reaches to its `:`, and the last part is a conditional again.
fn parse_cond(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 8usize,
{
    let (c, p) = match parse_or(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if p < toks.len() && toks[p] == Tok::Question {
        let (a, q) = match parse_implies(toks, p + 1, line) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        if q < toks.len() && toks[q] == Tok::Colon {
            match parse_cond(toks, q + 1, line) {
                Ok((b, r)) => Ok((Expr::Cond(Box::new(c), Box::new(a), Box::new(b)), r)),
                Err(e) => Err(e),
            }
        } else {
            Err(Refusal::Syntax(line))
        }
    } else {
        Ok((c, p))
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
    while p < toks.len() && (toks[p] == Tok::Op(BinOp::Mul) || toks[p] == Tok::Op(BinOp::Div) || toks[p] == Tok::Op(BinOp::Rem))
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        let op = if toks[p] == Tok::Op(BinOp::Mul) {
            BinOp::Mul
        } else if toks[p] == Tok::Op(BinOp::Div) {
            BinOp::Div
        } else {
            BinOp::Rem
        };
        match parse_unary(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(op, Box::new(a), Box::new(b));
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

/// A token that follows an atom: `.size()`, `.name` or `[`.
fn is_postfix(t: Tok) -> bool {
    match t {
        Tok::Size | Tok::Field(_) | Tok::HasValue | Tok::Value | Tok::Empty | Tok::LBracket => true,
        _ => false,
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
    while p < toks.len() && is_postfix(toks[p])
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        if toks[p] == Tok::Size {
            a = Expr::Size(Box::new(a));
            p = p + 1;
        } else if let Tok::Field(f) = toks[p] {
            if toks.len() - p > 2 && toks[p + 1] == Tok::LParen && toks[p + 2] == Tok::RParen {
                assert(!unknown_args(Args::Nil));
                a = Expr::MApply(Box::new(a), f, Box::new(Args::Nil));
                p = p + 3;
            } else if toks.len() - p > 1 && toks[p + 1] == Tok::LParen {
                match parse_args(toks, p + 2, line) {
                    Ok((args, q)) => {
                        a = Expr::MApply(Box::new(a), f, Box::new(args));
                        p = q;
                    },
                    Err(e) => return Err(e),
                }
            } else {
                a = Expr::Field(Box::new(a), f);
                p = p + 1;
            }
        } else if toks[p] == Tok::HasValue {
            a = Expr::HasValue(Box::new(a));
            p = p + 1;
        } else if toks[p] == Tok::Value {
            a = Expr::Value(Box::new(a));
            p = p + 1;
        } else if toks[p] == Tok::Empty {
            a = Expr::Empty(Box::new(a));
            p = p + 1;
        } else if toks.len() - p > 1 && toks[p + 1] == Tok::DotDot {
            match parse_implies(toks, p + 2, line) {
                Ok((j, q)) => if q < toks.len() && toks[q] == Tok::RBracket {
                    a = Expr::Prefix(Box::new(a), Box::new(j));
                    p = q + 1;
                } else {
                    return Err(Refusal::Syntax(line));
                },
                Err(e) => return Err(e),
            }
        } else {
            match parse_implies(toks, p + 1, line) {
                Ok((i, q)) => if q < toks.len() && toks[q] == Tok::RBracket {
                    a = Expr::Index(Box::new(a), Box::new(i));
                    p = q + 1;
                } else if q < toks.len() && toks[q] == Tok::DotDot {
                    if toks.len() - q > 1 && toks[q + 1] == Tok::RBracket {
                        a = Expr::Suffix(Box::new(a), Box::new(i));
                        p = q + 2;
                    } else {
                        match parse_implies(toks, q + 1, line) {
                            Ok((j, r)) => if r < toks.len() && toks[r] == Tok::RBracket {
                                a = Expr::Slice(Box::new(a), Box::new(i), Box::new(j));
                                p = r + 1;
                            } else {
                                return Err(Refusal::Syntax(line));
                            },
                            Err(e) => return Err(e),
                        }
                    }
                } else {
                    return Err(Refusal::Syntax(line));
                },
                Err(e) => return Err(e),
            }
        }
    }
    Ok((a, p))
}

/// The bound names of a `forall` or an `exists`, each parted by a comma, then `::` and the body, decision 0082. `forall i, j :: P`
/// is `forall i :: forall j :: P`.
fn parse_binders(toks: &Vec<Tok>, pos: usize, all: bool, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 10usize,
{
    if toks.len() - pos < 2 {
        return Err(Refusal::Syntax(line));
    }
    let j = match toks[pos] {
        Tok::Ident(j) => j,
        _ => return Err(Refusal::Syntax(line)),
    };
    let inner = if toks[pos + 1] == Tok::ColonColon {
        parse_implies(toks, pos + 2, line)
    } else if toks[pos + 1] == Tok::Comma {
        parse_binders(toks, pos + 2, all, line)
    } else {
        Err(Refusal::Syntax(line))
    };
    match inner {
        // The body of a quantifier reaches to the end of the line, or to the bracket, comma or colon that closes what holds it. A
        // body that stops before them would leave the rest of the line outside the quantifier, so the line is refused.
        Ok((body, p)) => if p < toks.len() && !(toks[p] == Tok::RParen || toks[p] == Tok::RBracket || toks[p] == Tok::Comma
            || toks[p] == Tok::Colon) {
            Err(Refusal::Syntax(line))
        } else if all {
            Ok((Expr::Forall(j, Box::new(body)), p))
        } else {
            Ok((Expr::Exists(j, Box::new(body)), p))
        },
        Err(e) => Err(e),
    }
}

/// What a parse of arguments gives: the arguments, and the place after the `)`. No unknown node is in them.
pub open spec fn parsed_args(r: Result<(Args, usize), Refusal>, toks: Seq<Tok>, pos: usize) -> bool {
    match r {
        Ok((a, p)) => pos < p && p <= toks.len() && !unknown_args(a),
        Err(_) => true,
    }
}

/// The arguments of a call, after its `(` and to its `)`, each parted by a comma. At least one argument is here.
fn parse_args(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Args, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed_args(r, toks@, pos),
    decreases toks.len() - pos, 10usize,
{
    match parse_implies(toks, pos, line) {
        Ok((a, p)) => if p < toks.len() && toks[p] == Tok::RParen {
            assert(!unknown_args(Args::Nil));
            Ok((Args::Cons(Box::new(a), Box::new(Args::Nil)), p + 1))
        } else if p < toks.len() && toks[p] == Tok::Comma {
            match parse_args(toks, p + 1, line) {
                Ok((rest, q)) => Ok((Args::Cons(Box::new(a), Box::new(rest)), q)),
                Err(e) => Err(e),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
        Err(e) => Err(e),
    }
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
        Tok::Bool(b) => Ok((Expr::Bool(b), pos + 1)),
        Tok::Ident(n) => if toks.len() - pos > 2 && toks[pos + 1] == Tok::LParen && toks[pos + 2] == Tok::RParen {
            assert(!unknown_args(Args::Nil));
            Ok((Expr::Apply(n, Box::new(Args::Nil)), pos + 3))
        } else if toks.len() - pos > 1 && toks[pos + 1] == Tok::LParen {
            match parse_args(toks, pos + 2, line) {
                Ok((args, p)) => Ok((Expr::Apply(n, Box::new(args)), p)),
                Err(e) => Err(e),
            }
        } else {
            Ok((Expr::Name(n), pos + 1))
        },
        Tok::Result => Ok((Expr::Result, pos + 1)),
        Tok::LParen => match parse_implies(toks, pos + 1, line) {
            Ok((e, p)) => if p < toks.len() && toks[p] == Tok::RParen {
                Ok((e, p + 1))
            } else {
                Err(Refusal::Syntax(line))
            },
            Err(e) => Err(e),
        },
        Tok::Old => if toks.len() - pos > 1 && toks[pos + 1] == Tok::LParen {
            match parse_implies(toks, pos + 2, line) {
                Ok((e, p)) => if p < toks.len() && toks[p] == Tok::RParen {
                    Ok((Expr::Old(Box::new(e)), p + 1))
                } else {
                    Err(Refusal::Syntax(line))
                },
                Err(e) => Err(e),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
        Tok::Forall => parse_binders(toks, pos + 1, true, line),
        Tok::Exists => parse_binders(toks, pos + 1, false, line),
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

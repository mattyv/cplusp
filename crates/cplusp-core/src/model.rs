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

// ------------------------------------------------------------------ lists, decision 0121

/// A list of items, in their order. Every list of the model is one, decision 0121.
#[derive(PartialEq, Eq, Debug)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

/// The value of the first pair with the key `k`.
pub open spec fn spec_get<V>(l: List<(u32, V)>, k: u32) -> Option<V>
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if n == k {
            Some(v)
        } else {
            spec_get(*rest, k)
        },
    }
}

pub fn get<V: Copy>(l: &List<(u32, V)>, k: u32) -> (r: Option<V>)
    ensures
        r == spec_get(*l, k),
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if *n == k {
            Some(*v)
        } else {
            get(rest, k)
        },
    }
}

/// The value of the first pair with the key `k`, by reference.
pub fn get_ref<V>(l: &List<(u32, V)>, k: u32) -> (r: Option<&V>)
    ensures
        match r {
            Some(v) => spec_get(*l, k) == Some(*v),
            None => spec_get(*l, k) is None,
        },
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if *n == k {
            Some(v)
        } else {
            get_ref(rest, k)
        },
    }
}

/// `k` is in the list.
pub open spec fn spec_has(l: List<u32>, k: u32) -> bool
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(n, rest) => n == k || spec_has(*rest, k),
    }
}

pub fn has(l: &List<u32>, k: u32) -> (r: bool)
    ensures
        r == spec_has(*l, k),
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(n, rest) => *n == k || has(rest, k),
    }
}

/// The keys of a list of pairs, in their order.
pub open spec fn spec_keys<V>(l: List<(u32, V)>) -> List<u32>
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons((n, _), rest) => List::Cons(n, Box::new(spec_keys(*rest))),
    }
}

pub fn keys<V>(l: &List<(u32, V)>) -> (r: List<u32>)
    ensures
        r == spec_keys(*l),
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons((n, _), rest) => List::Cons(*n, Box::new(keys(rest))),
    }
}

/// The items of `a`, then the items of `b`.
pub open spec fn spec_append<T>(a: List<T>, b: List<T>) -> List<T>
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(x, rest) => List::Cons(x, Box::new(spec_append(*rest, b))),
    }
}

pub fn append<T>(a: List<T>, b: List<T>) -> (r: List<T>)
    ensures
        r == spec_append(a, b),
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(x, rest) => List::Cons(x, Box::new(append(*rest, b))),
    }
}

/// A copy of a list of plain items.
pub fn copy<T: Copy>(l: &List<T>) -> (r: List<T>)
    ensures
        r == *l,
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons(x, rest) => List::Cons(*x, Box::new(copy(rest))),
    }
}

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

/// A type of the subset. `I8`, `I16` and `U16` are `int8_t`, `int16_t` and `uint16_t`, decision 0106. `Seq` is a read-only sequence of a scalar with its extent, a parameter only, decisions 0064 and 0070.
/// `Struct` is a struct of the file by its key, decision 0073. `Opt` is a `std::optional` of a scalar, decision 0075. `This` is the
/// object of a `const` member function of the struct by its key, a parameter by value, decision 0089. `ThisMut` is the object of a
/// member function that writes it, which takes it in and gives it back, decision 0096. `ThisAfter` is that object after the call,
/// as an ensures line reads it, and `Fresh` is the result of a constructor before it exists, as its requires line reads it. The
/// translator makes these two views itself. `Mut` is a reference parameter that the function writes, which takes a value in and
/// gives it back, and `MutAfter` is its value after the call, as an ensures line reads it, decision 0108. `MutSeq` is a vector by
/// reference that the function writes, as a sequence, and `MutSeqAfter` is its value after the call, decision 0145. `Enum` is an enum class of
/// the file by its key, decision 0109. `Void` is the result type
/// of a function that gives no value. `Other` is a type the translator has no rule for, by the id of its name.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Ty {
    I32,
    I64,
    U8,
    U32,
    U64,
    I8,
    I16,
    U16,
    Bool,
    Seq(Scalar, Extent),
    Struct(u32),
    Opt(Scalar),
    This(u32),
    ThisMut(u32),
    ThisAfter(u32),
    Mut(Scalar),
    MutAfter(Scalar),
    MutSeq(Scalar),
    MutSeqAfter(Scalar),
    Ptr(Scalar),
    Own(Scalar),
    Enum(u32),
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
/// `c ? a : b`, decision 0098. `Shr` is `a >> n` in code, with the type of its result, decision 0106. `Enumerator` is an enumerator,
/// by the key of its enum and its place among the enumerators, decision 0109. `CountIf` is `std::count_if(v.begin(), v.end(), f)` in
/// code, with the sequence, the name and the type of the parameter of the lambda `f`, and the expression of its one `return`,
/// decision 0149. `Unknown` is a construct with no rule, by the id of its kind and its line.
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
    Shr(Box<Expr>, Box<Expr>, Ty),
    Enumerator(u32, u32),
    CountIf(Box<Expr>, u32, Ty, Box<Expr>),
    Unknown(u32, u32),
}

pub type Args = List<Box<Expr>>;

/// A statement of the body, with its line. `Local` declares a name of a type with a start value. `Assign` writes a name. `Step`
/// adds one to a name of a type, or takes one away when its flag is false. `While` is a condition, the contract lines above the loop
/// and the body. `For` is a start, a condition, a step, the contract lines and the body, decision 0061. `SetField` writes a field of
/// the object of a member function, and `SetRefField` a field of a reference parameter, decision 0108. `Switch` is a switch over an
/// enum, by the key of the enum, with its cases, decision 0109. `Call` is a call that stands alone as a statement, by the key of its callee, the id of its
/// name and its arguments. `Exit` is `return;`, decision 0096. `Assert` is a `//@ assert` line in the body, and `Apply` is a
/// `//@ apply` line that calls a lemma of the companion file by the id of its name, decision 0099. `RangeFor` is a range-for, decision
/// 0143. `SetIndex` is `v[i] = e` of a vector by reference, decision 0145, and `PushBack` is `v.push_back(e)`, decision 0148.
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
    SetRefField(u32, u32, Expr, u32),
    Switch(Expr, u32, Box<Cases>, u32),
    Call(u32, u32, Box<Args>, u32),
    Exit(u32),
    Assert(Expr, u32),
    Apply(u32, Box<Args>, u32),
    RangeFor(u32, u32, Ty, Expr, Box<Conds>, Box<Stmts>, u32),
    SetIndex(u32, Expr, Expr, u32),
    PushBack(u32, Expr, u32),
    Unknown(u32, u32),
}

pub type Stmts = List<Box<Stmt>>;

/// The cases of a switch, each by the place of its enumerator among the enumerators, with its body, decision 0109. The plugin drops a
/// `break` that ends a case.
pub type Cases = List<(u32, Box<Stmts>)>;

/// The names and types of the parameters of a function, or of the fields of a struct, in their order.
pub type Params = List<(u32, Ty)>;

/// What a contract line says. `Modifies` names one reference parameter that the function writes, decision 0108. `Other` is a word
/// the translator has no rule for yet, by the id of the word. `Bad` is a line that the shell could not cut or parse, with the refusal
/// it got.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CondKind {
    Requires,
    Ensures,
    Invariant,
    Decreases,
    Modifies,
    Index,
    Other(u32),
    Bad(Refusal),
}

/// The names of the parameters of a declaration, in their order.
pub type Names = List<u32>;

/// A contract line: what it says, its expression, its line, and the names of the parameters of the declaration it stands on,
/// decision 0060.
pub type Conds = List<(CondKind, Expr, u32, Names)>;

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
pub type Structs = List<(u32, (u32, Params, Members))>;

/// The member functions of a struct: the id of each name, the key of its function, and its return type and parameters when it is
/// pure, decisions 0090 and 0095. The unit computes which are pure from the functions themselves, `spec_mark`.
pub type Members = List<(u32, (u32, Option<(Ty, Params)>))>;

/// The model of each struct of a file: its key and Dafny fields, or the refusal.
pub type StructModels = List<Result<(u32, DParams), Refusal>>;

/// The functions of one file.
pub type Fns = List<Box<Function>>;

// ------------------------------------------------------------------ the Dafny side

#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum DTy {
    Int32,
    Int64,
    UInt8,
    UInt32,
    UInt64,
    Int8,
    Int16,
    UInt16,
    Bool,
    Seq(Scalar),
    Struct(u32),
    Opt(Scalar),
    Enum(u32),
    Void,
}

/// A Dafny expression. `AsInt` is `(e as int)`, the exact value of a machine integer. `Conv` is `(e as T)`, which Dafny proves
/// fits `T`. `IsSome` is `e.Some?`, `Get` is `e.value`, which Dafny proves holds a value, and `Nothing` and `Just` are `None` and
/// `Some(e)`. `Drop` is `s[k..]`, which Dafny proves is in range, decision 0078. `Apply` calls a function of the companion file,
/// decision 0079. `Take` is `s[..j]` and `Slice` is `s[i..j]`, decision 0085. `TDiv` and `TRem` are `trunc_div` and `trunc_rem`
/// on the exact integers. `DivIn` is `(trunc_div(a, b) as T)`, and `RemIn` is the remainder of `T`, which also needs the quotient to
/// fit `T`, decision 0088. `FCall` calls the function of a pure member function by its key, decision 0090. `After` is `this'`, the
/// object of a member function that writes it, as the body leaves it, decision 0096. `Out` is `x'`, a reference parameter as the body
/// leaves it, decision 0108. `Enumerator` is the constructor of an enumerator, decision 0109. `Ite` is `if c then a else b`, decision 0098.
/// `Temp` reads a temporary that a call before the statement set, decision 0104. `ShrIn` is `(shr(a, n, W) as T)`, a right shift
/// of the width `W`, decision 0106. `SetAt` is `s[i := e]`, which Dafny proves is in range, decision 0145. `Append` is `s + [e]`, decision 0148. `CountIf` is `CountIf(s, (x: T) => e)` of the prelude, decision 0149. A Dafny expression calls no
/// method.
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
    Out(u32),
    Enumerator(u32, u32),
    Ite(Box<DExpr>, Box<DExpr>, Box<DExpr>),
    Temp(u32),
    ShrIn(Box<DExpr>, Box<DExpr>, DTy, u32),
    SetAt(Box<DExpr>, Box<DExpr>, Box<DExpr>),
    Append(Box<DExpr>, Box<DExpr>),
    CountIf(Box<DExpr>, u32, DTy, Box<DExpr>),
}

/// The calls that run before a statement, in the order that they run: each sets a temporary of the statement by its number, of a
/// type, to the value of a method by its key with its arguments, decision 0104.
pub type DCalls = List<(u32, DTy, u32, DArgs)>;

pub type DArgs = List<DExpr>;

/// A Dafny statement. `Local` is `var x: T := e;`. `LocalCall` is `var x: T := m(args);`. `ReturnCall` is `result := m(args);
/// return;`, since Dafny takes no call in a `return`. `Assign` is `x := e;` and `AssignCall` is `x := m(args);`. `While` is the
/// condition, the invariants, the decreases lines and the body. `For` prints as its start, then a `while` whose body ends with the
/// step. The start and the step keep their own places, decision 0069. `SetField` is `this' := this'.(f := e);`. `SetOut` is
/// `x' := e;` and `SetOutField` is `x' := x'.(f := e);` of a reference parameter, decision 0108. `Update` calls a method that writes
/// back, `o, x := m(o, x, args);`, and `LocalUpdate` also sets a new local to the value it gives, decisions 0096 and 0108. The
/// arguments hold each argument of the call. `CallStmt` is `m(args);` of a method that gives no value, and `Exit` is `return;`, decision 0096. `Assert` is
/// `assert e;` and `Apply` is `l(args);` of a lemma, decision 0099. `Match` is a match over the enum with the key, decision 0109. `Pre` is a statement with the calls that run before it, decision
/// 0104.
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
    SetOut(u32, DExpr),
    SetOutField(u32, u32, DExpr),
    Update(Objs, u32, DArgs),
    LocalUpdate(u32, DTy, Objs, u32, DArgs),
    CallStmt(u32, DArgs),
    Exit,
    Assert(DExpr),
    Apply(u32, DArgs),
    Match(DExpr, u32, Box<DCases>),
    Pre(DCalls, Box<DStmt>),
}

/// A place that a call writes back: a local by its name, the object of the member function that makes the call, or a reference
/// parameter of that function, decision 0108.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Obj {
    Local(u32),
    Object,
    Out(u32),
}

/// The places that a call writes back, in the order of the results of its method after `result`: the object, then each reference
/// parameter, decision 0108.
pub type Objs = List<Obj>;

/// The statements of a Dafny body. Each keeps the place of the C++ statement it comes from, decision 0068.
pub type DStmts = List<(Box<DStmt>, u32)>;

/// The cases of a match, each by the place of its constructor, with its body, decision 0109.
pub type DCases = List<(u32, Box<DStmts>)>;

pub type DParams = List<(u32, DTy)>;

/// Contract lines of a Dafny method or loop. Each keeps the place of the C++ contract line it comes from, decision 0068.
pub type DConds = List<(DExpr, u32)>;

/// A Dafny method. `function` is the body of the Dafny function of a pure member function, decision 0090. `writes` holds when the
/// method takes its object in and gives it back as `this'`, decision 0096. `outs` are the reference parameters that it gives back,
/// decision 0108. `trusted` holds for the method of a trusted function: it has
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
    pub outs: DParams,
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

pub type Models = List<Model>;

/// Why the translator refused. `Construct` is a node with no rule: the id of its kind and its line. `Name` is a name in a contract
/// that is no parameter. `Syntax` is a contract line the parser cannot read. `Backslash` is a contract line that ends in a backslash.
/// `Callee` is a call to a function with no method, by the id of the callee's name. `Place` is a call that does not stand alone.
/// `Twice` is a name declared a second time in a function. `Convert` is a cast between `bool` and a number. `WriteParam` is a write
/// to a parameter. `NoVar` is a name in a loop contract that is no variable. `Misplaced` is a contract line in the wrong place.
/// `SeqParam` is a sequence that is no parameter. `Extent` is a sequence made from one whose length or element differs.
/// `NoField` is a field of a contract that its struct does not have. `HoldsSeq` is a local or a result of a struct that holds a
/// sequence, decision 0076. `Element` is an optional of a struct or a sequence of `bool`, which have no rule, decisions 0064 and 0076.
/// `NotPure` is a contract that calls a member function that is not pure, or no member function, by the id of the name, decision
/// 0090. `NoTarget` is a call that writes a value back to a place that is no local and no reference parameter, by the line. `NoObject`
/// is a field or a member function in a requires line of a constructor, before the object exists, by the id of the name, decision
/// 0096. `NotRef` is a name on a modifies line that is no reference parameter, and `Unlisted` is a reference parameter that no
/// modifies line names, decision 0108. `PassOn` is a vector by reference that a call passes on to a parameter that writes it, by the
/// id of its name, decision 0147.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Refusal {
    Construct(u32, u32),
    Name(u32, u32),
    Syntax(u32),
    Backslash(u32),
    Callee(u32, u32),
    Place(u32),
    Twice(u32, u32),
    IndexName(u32, u32),
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
    NotRef(u32, u32),
    Unlisted(u32, u32),
    PassOn(u32, u32),
}

// ------------------------------------------------------------------ the rules

/// The id of the name `operator()`. The shell gives this id to that text, decision 0098.
pub const CALL_OP: u32 = 0;

/// The Dafny type of a scalar, decision 0108.
pub open spec fn spec_scalar_dty(s: Scalar) -> DTy {
    match s {
        Scalar::I32 => DTy::Int32,
        Scalar::I64 => DTy::Int64,
        Scalar::U8 => DTy::UInt8,
        Scalar::U32 => DTy::UInt32,
        Scalar::U64 => DTy::UInt64,
        Scalar::Bool => DTy::Bool,
        Scalar::Struct(k) => DTy::Struct(k),
    }
}

/// A type of the subset maps to its Dafny newtype, decision 0029 and the battery case signed_overflow. A reference parameter has the
/// type of its value, decision 0108.
pub open spec fn spec_ty(t: Ty, line: u32) -> Result<DTy, Refusal> {
    match t {
        Ty::I32 => Ok(DTy::Int32),
        Ty::I64 => Ok(DTy::Int64),
        Ty::U8 => Ok(DTy::UInt8),
        Ty::U32 => Ok(DTy::UInt32),
        Ty::U64 => Ok(DTy::UInt64),
        Ty::I8 => Ok(DTy::Int8),
        Ty::I16 => Ok(DTy::Int16),
        Ty::U16 => Ok(DTy::UInt16),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        Ty::Opt(s) => Ok(DTy::Opt(s)),
        // A pointer to const is an Option in Dafny, decisions 0140 and 0141.
        Ty::Ptr(s) => Ok(DTy::Opt(s)),
        // A unique_ptr is an Option in Dafny too, decision 0142.
        Ty::Own(s) => Ok(DTy::Opt(s)),
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::ThisMut(k) => Ok(DTy::Struct(k)),
        Ty::ThisAfter(k) => Ok(DTy::Struct(k)),
        Ty::Mut(s) => Ok(spec_scalar_dty(s)),
        Ty::MutAfter(s) => Ok(spec_scalar_dty(s)),
        Ty::MutSeq(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::MutSeqAfter(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::MutSeq(s) => Ok(DTy::Seq(s)),
        Ty::MutSeqAfter(s) => Ok(DTy::Seq(s)),
        Ty::Enum(k) => Ok(DTy::Enum(k)),
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
            Ty::Mut(_) => Err(Refusal::Syntax(line)),
            Ty::MutAfter(_) => Err(Refusal::Syntax(line)),
            Ty::MutSeq(_) => Err(Refusal::Syntax(line)),
            Ty::MutSeqAfter(_) => Err(Refusal::Syntax(line)),
            Ty::Ptr(_) => Err(Refusal::Syntax(line)),
            Ty::Struct(k) => if spec_holds(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            // An optional of a struct that holds a sequence stays out, decision 0137.
            Ty::Opt(Scalar::Struct(k)) => if spec_holds(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            Ty::Own(Scalar::Struct(k)) => if spec_holds(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            _ => Ok(dt),
        },
    }
}

/// The fields of the struct `k` in the table of the file.
pub open spec fn spec_fields_of(sd: Structs, k: u32) -> Option<Params> {
    match spec_get(sd, k) {
        Some((_, fields, _)) => Some(fields),
        None => None,
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
        List::Nil => false,
        List::Cons((_, t), rest) => (match t {
            Ty::Seq(_, _) => true,
            Ty::Struct(k) => depth == 0 || match spec_fields_of(sd, k) {
                Some(fs) => spec_holds_any(sd, fs, (depth - 1) as nat),
                None => false,
            },
            _ => false,
        }) || spec_holds_any(sd, *rest, depth),
    }
}

/// `x == nullptr` is no value in `x`, and `x != nullptr` is a value, decision 0140.
pub open spec fn spec_null_test(op: BinOp, d: DExpr) -> DExpr {
    if op == BinOp::Eq {
        DExpr::Not(Box::new(DExpr::IsSome(Box::new(d))))
    } else {
        DExpr::IsSome(Box::new(d))
    }
}

pub fn null_test(op: BinOp, d: DExpr) -> (r: DExpr)
    ensures
        r == spec_null_test(op, d),
{
    if op == BinOp::Eq {
        DExpr::Not(Box::new(DExpr::IsSome(Box::new(d))))
    } else {
        DExpr::IsSome(Box::new(d))
    }
}

/// A variable of pointer type in code. No operator takes one, except the test against nullptr, decision 0141.
// ponytail: it sees a bare variable only. The plugin refuses every other pointer operand by its type. Upgrade: look through Paren
// and Cond, as spec_ptr_operand does.
pub open spec fn spec_ptr_var(e: Expr) -> bool {
    e is Var && (e->Var_1 is Ptr || e->Var_1 is Own)
}

impl Expr {
    pub fn is_ptr_var(&self) -> (r: bool)
        ensures
            r == spec_ptr_var(*self),
    {
        match self {
            Expr::Var(_, Ty::Ptr(_)) | Expr::Var(_, Ty::Own(_)) => true,
            _ => false,
        }
    }

    pub fn is_nullopt(&self) -> (r: bool)
        ensures
            r == (*self is Nullopt),
    {
        match self {
            Expr::Nullopt => true,
            _ => false,
        }
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

/// The scalar of the elements of a sequence parameter, read-only or written, decisions 0064 and 0145.
pub open spec fn spec_seq_elem(t: Ty) -> Option<Scalar> {
    match t {
        Ty::Seq(s, _) => Some(s),
        Ty::MutSeq(s) => Some(s),
        _ => None,
    }
}

pub fn seq_elem(t: Ty) -> (r: Option<Scalar>)
    ensures
        r == spec_seq_elem(t),
{
    match t {
        Ty::Seq(s, _) => Some(s),
        Ty::MutSeq(s) => Some(s),
        _ => None,
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
        (Ty::Ptr(a), Ty::Ptr(b)) => a == b,
        (Ty::Own(a), Ty::Own(b)) => a == b,
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
    t == Ty::I32 || t == Ty::I64 || t == Ty::U8 || t == Ty::U32 || t == Ty::U64 || t == Ty::I8 || t == Ty::I16 || t == Ty::U16
}

/// The width in bits of an integer type, decision 0106.
pub open spec fn spec_width(t: Ty) -> u32 {
    match t {
        Ty::I8 => 8,
        Ty::U8 => 8,
        Ty::I16 => 16,
        Ty::U16 => 16,
        Ty::I32 => 32,
        Ty::U32 => 32,
        _ => 64,
    }
}

/// `a >> n` of code on the integer type `t`, decision 0106: `shr` of both operands as exact integers, with the width of `t`.
pub open spec fn spec_shift(da: DExpr, dn: DExpr, t: Ty, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !is_integer(t) {
            Err(Refusal::Convert(line))
        } else {
            Ok(DExpr::ShrIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(dn))), dt, spec_width(t)))
        },
    }
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

/// An expression of code where a call has no place, such as a loop condition, decision 0104.
pub open spec fn spec_code(e: Expr, line: u32) -> Result<DExpr, Refusal> {
    match spec_lift(e, List::Nil, line, List::Nil, 0, false) {
        Ok((_, d, _)) => Ok(d),
        Err(r) => Err(r),
    }
}

/// A statement with the calls that run before it. With no call it is the statement alone.
pub open spec fn spec_pre(c: DCalls, s: DStmt) -> DStmt {
    match c {
        List::Nil => s,
        _ => DStmt::Pre(c, Box::new(s)),
    }
}

/// The type of the value of the callee `key`: a value type, decision 0064, or the struct that a constructor builds, decision 0105.
pub open spec fn spec_callee_ty(all: Fns, key: u32, line: u32, sd: Structs) -> Result<DTy, Refusal> {
    match spec_find(all, key) {
        Some(f) => match f.ret {
            Ty::This(_) => spec_ret_ty(f.ret, line, sd),
            _ => spec_value_ty(f.ret, line, sd),
        },
        None => Err(Refusal::Syntax(line)),
    }
}

/// An expression of code, decision 0058. Each call that C++ evaluates once runs before the statement and sets a temporary,
/// numbered from `n`, which the expression reads, decision 0104. Where `open` is false, a call has no place: on the right of `&&`
/// or `||`, in a branch of `?:`, and in a loop condition. A call of a function that writes its object has no place in an
/// expression. The operators stay the machine operators of their newtype, so Dafny checks each step for overflow, the battery case
/// signed_overflow. A contract name or `result` has no place in code. The result is the calls, the expression and the next number.
pub open spec fn spec_lift(e: Expr, all: Fns, line: u32, sd: Structs, n: u32, open: bool) -> Result<(DCalls, DExpr, u32), Refusal>
    decreases e,
{
    match e {
        Expr::Lit(v, t) => match spec_ty(t, line) {
            Ok(dt) => Ok((List::Nil, DExpr::Conv(dt, Box::new(DExpr::Lit(v))), n)),
            Err(r) => Err(r),
        },
        Expr::Bool(v) => Ok((List::Nil, DExpr::Bool(v), n)),
        Expr::Enumerator(k, i) => Ok((List::Nil, DExpr::Enumerator(k, i), n)),
        Expr::Var(v, t) => match spec_ty(t, line) {
            Ok(_) => Ok((List::Nil, spec_code_var(v, t), n)),
            Err(r) => Err(r),
        },
        Expr::Call(k, nm, args, at) => if !open || spec_callee_writes(all, k) {
            Err(Refusal::Place(at))
        } else if !spec_callable(all, k, sd) {
            Err(Refusal::Callee(nm, at))
        } else {
            match spec_lift_args(*args, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match spec_callee_ty(all, k, line, sd) {
                    Err(r) => Err(r),
                    Ok(dt) => if n1 < 0xFFFF_FFFF {
                        Ok((spec_append(ca, List::Cons((n1, dt, k, da), Box::new(List::Nil))), DExpr::Temp(n1), (n1 + 1) as u32))
                    } else {
                        Err(Refusal::Syntax(line))
                    },
                },
            }
        },
        // A comparison with nullptr tests for a value, decision 0140.
        Expr::Bin(op, a, b) if (op == BinOp::Eq || op == BinOp::Ne) && (*a is Nullopt || *b is Nullopt) => if *b is Nullopt {
            match spec_lift(*a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => Ok((ca, spec_null_test(op, da), n1)),
            }
        } else {
            match spec_lift(*b, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((cb, db, n1)) => Ok((cb, spec_null_test(op, db), n1)),
            }
        },
        Expr::Bin(op, a, b) => if op == BinOp::Div || op == BinOp::Rem || spec_ptr_var(*a) || spec_ptr_var(*b) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_lift(*a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open && !(op == BinOp::And || op == BinOp::Or)) {
                    Err(r) => Err(r),
                    Ok((cb, db, n2)) => Ok((spec_append(ca, cb), DExpr::Bin(op, Box::new(da), Box::new(db)), n2)),
                },
            }
        },
        Expr::Divide(op, a, b, t) => if !(op == BinOp::Div || op == BinOp::Rem) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_lift(*a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open) {
                    Err(r) => Err(r),
                    Ok((cb, db, n2)) => match spec_divide(op, da, db, t, line) {
                        Err(r) => Err(r),
                        Ok(d) => Ok((spec_append(ca, cb), d, n2)),
                    },
                },
            }
        },
        Expr::Shr(a, b, t) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cb, db, n2)) => match spec_shift(da, db, t, line) {
                    Err(r) => Err(r),
                    Ok(d) => Ok((spec_append(ca, cb), d, n2)),
                },
            },
        },
        Expr::Not(a) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Not(Box::new(d)), n1)),
        },
        Expr::Neg(a) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Neg(Box::new(d)), n1)),
        },
        Expr::Cast(ck, a) => match ck {
            CastKind::Other(k) => Err(Refusal::Construct(k, line)),
            CastKind::Integral(from, to) => match spec_lift(*a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((c, d, n1)) => match spec_integral(from, to, d, line) {
                    Err(r) => Err(r),
                    Ok(di) => Ok((c, di, n1)),
                },
            },
            _ => spec_lift(*a, all, line, sd, n, open),
        },
        Expr::Paren(a) => spec_lift(*a, all, line, sd, n, open),
        Expr::Brace(a) => spec_lift(*a, all, line, sd, n, open),
        Expr::Size(o) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(d)))), n1)),
        },
        // `std::count_if(v.begin(), v.end(), f)` is CountIf of the prelude, as the int64 that C++ gives, decision 0149. `v` is a
        // sequence parameter, the parameter of the lambda has the element type, and its test holds no call.
        Expr::CountIf(o, x, xt, t) => match *o {
            Expr::Var(v, vt) => match spec_seq_elem(vt) {
                Some(s) => if spec_elem(s) == xt {
                    match spec_ty(xt, line) {
                        Err(r) => Err(r),
                        Ok(dx) => match spec_lift(*t, List::Nil, line, List::Nil, 0, false) {
                            Err(r) => Err(r),
                            Ok((_, dt, _)) => Ok((List::Nil, DExpr::Conv(DTy::Int64, Box::new(DExpr::CountIf(Box::new(spec_code_var(v, vt)), x, dx, Box::new(dt)))), n)),
                        },
                    }
                } else {
                    Err(Refusal::Syntax(line))
                },
                None => Err(Refusal::Syntax(line)),
            },
            _ => Err(Refusal::Syntax(line)),
        },
        Expr::Index(o, i) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((co, d, n1)) => match spec_lift(*i, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((ci, di, n2)) => Ok((spec_append(co, ci), DExpr::Index(Box::new(d), Box::new(di)), n2)),
            },
        },
        Expr::Copy(a, from, to) => if copies(from, to) {
            spec_lift(*a, all, line, sd, n, open)
        } else {
            Err(Refusal::Extent(line))
        },
        Expr::Field(o, f) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Field(Box::new(d), f), n1)),
        },
        Expr::Construct(k, args) => match spec_lift_args(*args, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, da, n1)) => Ok((c, DExpr::Ctor(k, Box::new(da)), n1)),
        },
        Expr::HasValue(o) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::IsSome(Box::new(d)), n1)),
        },
        Expr::Value(o) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Get(Box::new(d)), n1)),
        },
        Expr::Nullopt => Ok((List::Nil, DExpr::Nothing, n)),
        Expr::Wrap(a) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Just(Box::new(d)), n1)),
        },
        Expr::Empty(o) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0))), n1)),
        },
        Expr::Subspan(o, k) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((co, d, n1)) => match spec_lift(*k, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((ck, dk, n2)) => Ok((spec_append(co, ck), DExpr::Drop(Box::new(d), Box::new(dk)), n2)),
            },
        },
        Expr::Cond(cnd, a, b) => match spec_lift(*cnd, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, dc, n1)) => match spec_lift(*a, all, line, sd, n1, false) {
                Err(r) => Err(r),
                Ok((ca, da, n2)) => match spec_lift(*b, all, line, sd, n2, false) {
                    Err(r) => Err(r),
                    Ok((cb, db, n3)) => Ok((spec_append(c, spec_append(ca, cb)), DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db)), n3)),
                },
            },
        },
        Expr::Name(v) => Err(Refusal::Name(v, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(k, l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

/// The arguments of a call, each lifted in its order, decision 0104.
pub open spec fn spec_lift_args(args: Args, all: Fns, line: u32, sd: Structs, n: u32, open: bool) -> Result<(DCalls, DArgs, u32), Refusal>
    decreases args,
{
    match args {
        List::Nil => Ok((List::Nil, List::Nil, n)),
        List::Cons(a, rest) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match spec_lift_args(*rest, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cr, dr, n2)) => Ok((spec_append(ca, cr), List::Cons(da, Box::new(dr)), n2)),
            },
        },
    }
}

/// A call that stands alone, whose arguments may hold calls that run before it, decision 0104.
pub open spec fn spec_call_lift(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs) -> Result<(DCalls, DArgs), Refusal> {
    if spec_callable(all, key, sd) {
        match spec_lift_args(args, all, line, sd, 0, true) {
            Ok((c, da, _)) => Ok((c, da)),
            Err(r) => Err(r),
        }
    } else {
        Err(Refusal::Callee(name, at))
    }
}

/// A variable of code. The object of a member function that writes it is `this'` in the body, decision 0096, and a reference
/// parameter is `x'`, decision 0108.
pub open spec fn spec_code_var(v: u32, t: Ty) -> DExpr {
    match t {
        Ty::ThisMut(_) => DExpr::After,
        Ty::Mut(_) => DExpr::Out(v),
        Ty::MutSeq(_) => DExpr::Out(v),
        _ => DExpr::Var(v),
    }
}

/// A variable of a contract. The object after the call is `this'`, decision 0096, and a reference parameter after the call is `x'`,
/// decision 0108.
pub open spec fn spec_var(v: u32, t: Ty) -> DExpr {
    match t {
        Ty::ThisAfter(_) => DExpr::After,
        Ty::MutAfter(_) => DExpr::Out(v),
        Ty::MutSeqAfter(_) => DExpr::Out(v),
        _ => DExpr::Var(v),
    }
}

/// The type of the value of a variable of a contract: a reference parameter has the type of its value, decision 0108.
pub open spec fn spec_view_ty(t: Ty) -> Ty {
    match t {
        Ty::Mut(s) => spec_elem(s),
        Ty::MutAfter(s) => spec_elem(s),
        Ty::MutSeq(s) => Ty::Seq(s, Extent::Dynamic),
        Ty::MutSeqAfter(s) => Ty::Seq(s, Extent::Dynamic),
        _ => t,
    }
}

/// The parameter of the definition at the place where the declaration `decl` has the name `name`, decision 0060.
pub open spec fn spec_rebind(decl: Names, ps: Params, name: u32) -> Option<(u32, Ty)>
    decreases ps,
{
    match decl {
        List::Nil => None,
        List::Cons(d, drest) => match ps {
            List::Nil => None,
            List::Cons((p, t), prest) => if d == name {
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
        Expr::Enumerator(k, i) => Ok(DExpr::Enumerator(k, i)),
        Expr::Name(n) => if spec_has(bound, n) {
            Ok(DExpr::Bound(n))
        } else {
            match spec_rebind(decl, ps, n) {
                Some((p, t)) => spec_leaf(spec_var(p, t), spec_view_ty(t), line),
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
        // A comparison with nullptr tests an optional for a value, decision 0140.
        Expr::Bin(op, a, b) if (op == BinOp::Eq || op == BinOp::Ne) && (*a is Nullopt || *b is Nullopt) => if *b is Nullopt {
            match spec_path(*a, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Ptr(_))) => Ok(spec_null_test(op, d)),
                Ok((d, Ty::Own(_))) => Ok(spec_null_test(op, d)),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            }
        } else {
            match spec_path(*b, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Ptr(_))) => Ok(spec_null_test(op, d)),
                Ok((d, Ty::Own(_))) => Ok(spec_null_test(op, d)),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            }
        },
        Expr::Bin(op, a, b) if spec_ptr_operand(*a, decl, ps, ret, bound, line, sd) || spec_ptr_operand(*b, decl, ps, ret, bound, line, sd) => Err(
            Refusal::Syntax(line),
        ),
        Expr::Bin(op, a, b) => if spec_ordered(op) && (spec_enum_operand(*a, decl, ps, ret, bound, line, sd) || spec_enum_operand(
            *b,
            decl,
            ps,
            ret,
            bound,
            line,
            sd,
        )) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_contract(*a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(spec_binary(op, da, db)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
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
        Expr::Forall(j, body) => match spec_contract(*body, decl, ps, ret, List::Cons(j, Box::new(bound)), line, sd) {
            Ok(db) => Ok(DExpr::Forall(j, Box::new(db))),
            Err(r) => Err(r),
        },
        Expr::Exists(j, body) => match spec_contract(*body, decl, ps, ret, List::Cons(j, Box::new(bound)), line, sd) {
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
            Ok((d, Ty::Ptr(s))) => spec_leaf(DExpr::Get(Box::new(d)), spec_elem(s), line),
            Ok((d, Ty::Own(s))) => spec_leaf(DExpr::Get(Box::new(d)), spec_elem(s), line),
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
                    Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match spec_object(ps, ret) {
            Some((o, k)) => match spec_member(sd, k, f) {
                Some((key, Some((t, mps)))) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(o, Box::new(spec_convert(da, spec_tail(mps)))))), t, line),
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
                        Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    _ => Err(Refusal::NotPure(f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Chain(_, _, a, b, c) if spec_ptr_operand(*a, decl, ps, ret, bound, line, sd) || spec_ptr_operand(*b, decl, ps, ret, bound, line, sd)
            || spec_ptr_operand(*c, decl, ps, ret, bound, line, sd) => Err(Refusal::Syntax(line)),
        Expr::Chain(o1, o2, a, b, c) => if chains(o1, o2) && !(spec_enum_operand(*a, decl, ps, ret, bound, line, sd) || spec_enum_operand(
            *b,
            decl,
            ps,
            ret,
            bound,
            line,
            sd,
        ) || spec_enum_operand(*c, decl, ps, ret, bound, line, sd)) {
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
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match spec_contract_args(*rest, decl, ps, ret, bound, line, sd) {
                Ok(dr) => Ok(List::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// The type of the field `f` of the struct `k` in the table of the file.
pub open spec fn spec_field_ty(sd: Structs, k: u32, f: u32) -> Option<Ty> {
    match spec_fields_of(sd, k) {
        Some(fields) => spec_get(fields, f),
        None => None,
    }
}

/// A path of a contract that a field reads: a parameter, `result` or a field of a path, with its Dafny form and its type, decision
/// 0073. A bound name is an integer, so it has no field.
/// An order: `<`, `<=`, `>` or `>=`.
pub open spec fn spec_ordered(op: BinOp) -> bool {
    op == BinOp::Lt || op == BinOp::Le || op == BinOp::Gt || op == BinOp::Ge
}

/// An operand of a contract whose type is an enum, decision 0114. Dafny reads an order of two datatype values as an order of rank that
/// it does not know, so it proves no C++ order of enums, decision 0115. An order of enums has no rule.
pub open spec fn spec_enum_operand(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> bool
    decreases e, 1nat,
{
    match e {
        Expr::Enumerator(_, _) => true,
        Expr::Paren(a) => spec_enum_operand(*a, decl, ps, ret, bound, line, sd),
        Expr::Old(a) => spec_enum_operand(*a, decl, spec_before(ps), ret, bound, line, sd),
        Expr::Cond(_, a, b) => spec_enum_operand(*a, decl, ps, ret, bound, line, sd) || spec_enum_operand(*b, decl, ps, ret, bound, line, sd),
        Expr::Result => match ret {
            Some(Ty::Enum(_)) => true,
            _ => false,
        },
        _ => match spec_path(e, decl, ps, ret, bound, line, sd) {
            Ok((_, Ty::Enum(_))) => true,
            _ => false,
        },
    }
}

/// An operand that is a pointer, decision 0141, or a unique_ptr, decision 0142. No comparison or other operator takes one, except the test against nullptr.
pub open spec fn spec_ptr_operand(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> bool
    decreases e, 1nat,
{
    match e {
        Expr::Paren(a) => spec_ptr_operand(*a, decl, ps, ret, bound, line, sd),
        Expr::Old(a) => spec_ptr_operand(*a, decl, spec_before(ps), ret, bound, line, sd),
        Expr::Cond(_, a, b) => spec_ptr_operand(*a, decl, ps, ret, bound, line, sd) || spec_ptr_operand(*b, decl, ps, ret, bound, line, sd),
        _ => match spec_path(e, decl, ps, ret, bound, line, sd) {
            Ok((_, Ty::Ptr(_))) => true,
            Ok((_, Ty::Own(_))) => true,
            _ => false,
        },
    }
}

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
                Some((p, t)) => Ok((spec_var(p, t), spec_view_ty(t))),
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
        // The value of an optional of a struct is a struct, so `o->f` reads its field, decision 0137. Dafny checks that it holds a value.
        Expr::Value(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok((d, Ty::Ptr(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok((d, Ty::Own(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
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

/// The parameter `this` of a member function, with the key of its struct, decision 0089.
pub open spec fn spec_this(ps: Params) -> Option<(u32, u32)>
    decreases ps,
{
    match ps {
        List::Nil => None,
        List::Cons((p, t), rest) => match t {
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
        List::Cons((p, t), rest) => match t {
            Ty::This(_) => Some((p, t)),
            Ty::ThisMut(_) => Some((p, t)),
            Ty::ThisAfter(_) => Some((p, t)),
            _ => spec_self(*rest),
        },
        List::Nil => None,
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
        List::Nil => List::Nil,
        List::Cons((p, t), rest) => List::Cons((p, match t {
                Ty::ThisMut(k) => Ty::ThisAfter(k),
                Ty::Mut(s) => Ty::MutAfter(s),
                Ty::MutSeq(s) => Ty::MutSeqAfter(s),
                _ => t,
            }), Box::new(spec_after(*rest))),
    }
}

/// The parameters as `old()` reads them: the object before the call.
pub open spec fn spec_before(ps: Params) -> Params
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((p, t), rest) => List::Cons((p, match t {
                Ty::ThisAfter(k) => Ty::ThisMut(k),
                Ty::MutAfter(s) => Ty::Mut(s),
                Ty::MutSeqAfter(s) => Ty::MutSeq(s),
                _ => t,
            }), Box::new(spec_before(*rest))),
    }
}

/// The contract reads the object or a reference parameter after the call, so `old()` has a meaning: an ensures line of a function
/// that writes its object, decision 0096, or a reference parameter, decision 0108.
pub open spec fn spec_has_after(ps: Params) -> bool {
    match spec_self(ps) {
        Some((_, Ty::ThisAfter(_))) => true,
        _ => spec_any_after(ps),
    }
}

/// A reference parameter after the call is among the parameters, decision 0108.
pub open spec fn spec_any_after(ps: Params) -> bool
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => match t {
            Ty::MutAfter(_) => true,
            Ty::MutSeqAfter(_) => true,
            _ => spec_any_after(*rest),
        },
    }
}

/// `name` is a reference parameter that the function writes, decision 0108.
pub open spec fn spec_is_mut(ps: Params, name: u32) -> bool {
    match spec_get(ps, name) {
        Some(Ty::Mut(_)) => true,
        _ => false,
    }
}

/// A parameter takes a value in and gives it back: the object of a member function that writes it, decision 0096, or a reference
/// parameter, decision 0108.
pub open spec fn spec_written(t: Ty) -> bool {
    match t {
        Ty::ThisMut(_) => true,
        Ty::Mut(_) => true,
        Ty::MutSeq(_) => true,
        _ => false,
    }
}

/// The function gives back a value of a parameter, decisions 0096 and 0108.
pub open spec fn spec_mutates(ps: Params) -> bool
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => spec_written(t) || spec_mutates(*rest),
    }
}

/// The reference parameters that the function gives back, as Dafny parameters, decision 0108.
pub open spec fn spec_outs(ps: Params) -> DParams
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Mut(s) => List::Cons((n, spec_scalar_dty(s)), Box::new(spec_outs(*rest))),
            Ty::MutSeq(s) => List::Cons((n, DTy::Seq(s)), Box::new(spec_outs(*rest))),
            _ => spec_outs(*rest),
        },
    }
}

/// The modifies lines name each reference parameter and nothing else, decision 0108. A name reads the parameter of the definition at
/// its place in the declaration, decision 0060.
pub open spec fn spec_modifies(ps: Params, cs: Conds, line: u32) -> Option<Refusal> {
    match spec_bad_modifies(ps, cs) {
        Some(r) => Some(r),
        None => spec_unlisted(ps, ps, cs, line),
    }
}

/// The first modifies line that names no reference parameter.
pub open spec fn spec_bad_modifies(ps: Params, cs: Conds) -> Option<Refusal>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, decl), rest) => if k == CondKind::Modifies {
            match e {
                Expr::Name(n) => match spec_rebind(decl, ps, n) {
                    Some((_, Ty::Mut(_))) => spec_bad_modifies(ps, *rest),
                    Some((_, Ty::MutSeq(_))) => spec_bad_modifies(ps, *rest),
                    _ => Some(Refusal::NotRef(n, l)),
                },
                _ => Some(Refusal::Syntax(l)),
            }
        } else {
            spec_bad_modifies(ps, *rest)
        },
    }
}

/// A modifies line names the parameter `p`.
pub open spec fn spec_lists(ps: Params, cs: Conds, p: u32) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => (k == CondKind::Modifies && match e {
            Expr::Name(n) => match spec_rebind(decl, ps, n) {
                Some((q, _)) => q == p,
                None => false,
            },
            _ => false,
        }) || spec_lists(ps, *rest, p),
    }
}

/// The first reference parameter among `todo` that no modifies line names.
pub open spec fn spec_unlisted(todo: Params, ps: Params, cs: Conds, line: u32) -> Option<Refusal>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => match t {
            Ty::Mut(_) | Ty::MutSeq(_) => if spec_lists(ps, cs, p) {
                spec_unlisted(*rest, ps, cs, line)
            } else {
                Some(Refusal::Unlisted(p, line))
            },
            _ => spec_unlisted(*rest, ps, cs, line),
        },
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

/// The type of a parameter. The object after a call is a view of the contract, never a parameter. An optional of a struct that holds
/// a sequence stays out, decision 0137.
pub open spec fn spec_param_ty(t: Ty, line: u32, sd: Structs) -> Result<DTy, Refusal> {
    match t {
        Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
        Ty::MutAfter(_) => Err(Refusal::Syntax(line)),
        Ty::MutSeqAfter(_) => Err(Refusal::Syntax(line)),
        Ty::Opt(Scalar::Struct(k)) => if spec_holds(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            spec_ty(t, line)
        },
        Ty::Ptr(Scalar::Struct(k)) => if spec_holds(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            spec_ty(t, line)
        },
        Ty::Own(Scalar::Struct(k)) => if spec_holds(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            spec_ty(t, line)
        },
        _ => spec_ty(t, line),
    }
}

/// The parameters as Dafny parameters.
pub open spec fn spec_params(ps: Params, line: u32, sd: Structs) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        List::Cons((n, t), rest) => match spec_param_ty(t, line, sd) {
            Ok(dt) => match spec_params(*rest, line, sd) {
                Ok(dr) => Ok(List::Cons((n, dt), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

/// A function has a method when its parameters and its return type are in the subset, and its modifies lines name each reference
/// parameter and nothing else, decision 0108.
pub open spec fn has_signature(f: Function, sd: Structs) -> bool {
    spec_params(f.params, f.line, sd).is_ok() && spec_ret_ty(f.ret, f.line, sd).is_ok() && spec_modifies(f.params, f.conds, f.line) is None
}

/// A key names a function of the file that has a method.
pub open spec fn spec_callable(fs: Fns, key: u32, sd: Structs) -> bool
    decreases fs,
{
    match fs {
        List::Nil => false,
        List::Cons(f, rest) => (f.name == key && has_signature(*f, sd)) || spec_callable(*rest, key, sd),
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
        Stmt::RangeFor(_, _, _, _, _, _, l) => l,
        Stmt::SetField(_, _, l) => l,
        Stmt::SetRefField(_, _, _, l) => l,
        Stmt::Switch(_, _, _, l) => l,
        Stmt::Call(_, _, _, l) => l,
        Stmt::Exit(l) => l,
        Stmt::Assert(_, l) => l,
        Stmt::Apply(_, _, l) => l,
        Stmt::SetIndex(_, _, _, l) => l,
        Stmt::PushBack(_, _, l) => l,
        Stmt::Unknown(_, l) => l,
    }
}

/// The variables in scope after a statement, decision 0062: a local adds its name and type in front of the variables before it.
/// A local inside a branch or a loop body stays inside, so the scope after any other statement is the scope before it.
pub open spec fn spec_scope(s: Stmt, env: Params) -> Params {
    match s {
        Stmt::Local(n, t, _, _) => List::Cons((n, t), Box::new(env)),
        _ => env,
    }
}


/// The index of a range-for, decision 0143: the name on its index line with the line, or `fresh` and 0 when there is no index line.
/// A second index line, or an index line that holds no single name, is refused.
pub open spec fn spec_index_of(cs: Conds, fresh: u32) -> Result<(u32, u32), Refusal>
    decreases cs,
{
    match cs {
        List::Nil => Ok((fresh, 0)),
        List::Cons((k, e, l, _), rest) => match spec_index_of(*rest, fresh) {
            Err(r) => Err(r),
            Ok((n, l2)) => if k == CondKind::Index {
                if l2 != 0 {
                    Err(Refusal::Syntax(l2))
                } else {
                    match e {
                        Expr::Name(m) => Ok((m, l)),
                        _ => Err(Refusal::Syntax(l)),
                    }
                }
            } else {
                Ok((n, l2))
            },
        },
    }
}

/// The invariant `i <= v.size()` of a range-for, decision 0143.
pub open spec fn spec_range_bound(i: u32, v: u32) -> Expr {
    Expr::Bin(BinOp::Le, Box::new(Expr::Name(i)), Box::new(Expr::Size(Box::new(Expr::Name(v)))))
}

/// The decreases line `v.size() - i` of a range-for, decision 0143.
pub open spec fn spec_range_measure(i: u32, v: u32) -> Expr {
    Expr::Bin(BinOp::Sub, Box::new(Expr::Size(Box::new(Expr::Name(v)))), Box::new(Expr::Name(i)))
}

/// The test `i < v.size()` of a range-for, in code, decision 0143.
pub open spec fn spec_range_test(i: u32, v: u32, s: Scalar, ext: Extent) -> Expr {
    Expr::Bin(BinOp::Lt, Box::new(Expr::Var(i, Ty::U64)), Box::new(Expr::Size(Box::new(Expr::Var(v, Ty::Seq(s, ext))))))
}

/// The element `v[i]` that starts each turn of a range-for, in code, decision 0143.
pub open spec fn spec_range_elem(i: u32, v: u32, s: Scalar, ext: Extent) -> Expr {
    Expr::Index(Box::new(Expr::Var(v, Ty::Seq(s, ext))), Box::new(Expr::Var(i, Ty::U64)))
}

/// The start value 0 of the index of a range-for, decision 0143.
pub open spec fn spec_range_zero() -> DExpr {
    DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0)))
}

/// The lines of one kind of the contract of a loop, in their order, decisions 0061 and 0062. Each reads the variables `env` in scope
/// at the loop, and the object as the body leaves it, decision 0099. It has no
/// `result`. A `requires` or an `ensures` line has no place above a loop.
pub open spec fn spec_loop_conds(cs: Conds, want: CondKind, env: Params, sd: Structs, ranged: bool) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((k, e, l, _), rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Requires => Err(Refusal::Misplaced(l)),
            CondKind::Ensures => Err(Refusal::Misplaced(l)),
            CondKind::Modifies => Err(Refusal::Misplaced(l)),
            // An index line goes above a range-for only, decision 0143.
            CondKind::Index if !ranged => Err(Refusal::Misplaced(l)),
            _ => match spec_loop_conds(*rest, want, env, sd, ranged) {
                Ok(dr) => if k == want {
                    match spec_contract(e, spec_keys(env), spec_after(env), None, List::Nil, l, sd) {
                        Ok(d) => Ok(List::Cons((d, l), Box::new(dr))),
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

/// The callee with the key `key` gives back a value of a parameter: its object, decision 0096, or a reference parameter, decision
/// 0108.
pub open spec fn spec_callee_writes(all: Fns, key: u32) -> bool {
    match spec_find(all, key) {
        Some(f) => spec_mutates(f.params),
        None => false,
    }
}

/// A place that a call writes back, decisions 0096 and 0108: a local, the object of a member function that writes it, or a reference
/// parameter. A parameter by value is never written, and any other place has no rule yet.
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
            Ty::Mut(_) => if spec_is_mut(ps, v) {
                Ok(Obj::Out(v))
            } else {
                Err(Refusal::Syntax(line))
            },
            // A call that passes a vector by reference on to a writer has no rule yet, decision 0147.
            Ty::MutSeq(_) => Err(Refusal::PassOn(v, line)),
            _ => if (spec_get(ps, v) is Some) {
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

/// The places that a call writes back: the argument at each parameter `cps` of the callee that takes a value in and gives it back,
/// in order, decisions 0096 and 0108.
pub open spec fn spec_writebacks(args: Args, cps: Params, ps: Params, line: u32) -> Result<Objs, Refusal>
    decreases args,
{
    match args {
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match cps {
            List::Nil => Err(Refusal::Syntax(line)),
            List::Cons((_, t), crest) => if spec_written(t) {
                match spec_target(*a, ps, line) {
                    Err(r) => Err(r),
                    Ok(o) => match spec_writebacks(*rest, *crest, ps, line) {
                        Err(r) => Err(r),
                        Ok(os) => Ok(List::Cons(o, Box::new(os))),
                    },
                }
            } else {
                spec_writebacks(*rest, *crest, ps, line)
            },
        },
    }
}

/// The places that a call of the callee with the key `key` writes back.
pub open spec fn spec_callee_writebacks(all: Fns, key: u32, args: Args, ps: Params, line: u32) -> Result<Objs, Refusal> {
    match spec_find(all, key) {
        Some(f) => spec_writebacks(args, f.params, ps, line),
        None => Err(Refusal::Syntax(line)),
    }
}

/// A call that stands alone as a statement, decision 0096. A call of a function that gives back a value of a parameter writes each
/// such argument back, decision 0108. A call of any other function must give no value.
pub open spec fn spec_call_stmt(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    if spec_callee_writes(all, key) {
        match spec_callee_writebacks(all, key, args, ps, line) {
            Err(r) => Err(r),
            Ok(os) => match spec_call_lift(key, name, args, line, all, line, sd) {
                Ok((c, da)) => Ok(spec_pre(c, DStmt::Update(os, key, da))),
                Err(r) => Err(r),
            },
        }
    } else {
        match spec_call_lift(key, name, args, line, all, line, sd) {
            Ok((c, da)) => if spec_callee_void(all, key) {
                Ok(spec_pre(c, DStmt::CallStmt(key, da)))
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
        match spec_callee_writebacks(all, key, args, ps, line) {
            Err(r) => Err(r),
            Ok(os) => match spec_call_lift(key, name, args, at, all, line, sd) {
                Ok((c, da)) => Ok(spec_pre(c, DStmt::LocalUpdate(n, dt, os, key, da))),
                Err(r) => Err(r),
            },
        }
    } else {
        match spec_call_lift(key, name, args, at, all, line, sd) {
            Ok((c, da)) => Ok(spec_pre(c, DStmt::LocalCall(n, dt, key, da))),
            Err(r) => Err(r),
        }
    }
}

/// `++x` or `--x`: a local, or a reference parameter that the function writes, decision 0108.
pub open spec fn spec_step(n: u32, dt: DTy, up: bool, out: bool) -> DStmt {
    let op = if up {
        BinOp::Add
    } else {
        BinOp::Sub
    };
    let one = Box::new(DExpr::Conv(dt, Box::new(DExpr::Lit(1))));
    if out {
        DStmt::SetOut(n, DExpr::Bin(op, Box::new(DExpr::Out(n)), one))
    } else {
        DStmt::Assign(n, DExpr::Bin(op, Box::new(DExpr::Var(n)), one))
    }
}

/// A statement of the body, and a list of them. `env` is the variables in scope, and `ps` the parameters. A call runs before its
/// statement where C++ runs it once, decision 0104, and a call of a function that writes its object or gives no value stands
/// alone. A write is to a local, never to a parameter, or to a field of the object of a member function that writes it, decision
/// 0096.
// ponytail: `return o.f();` and `x = o.f();` of a function that writes its object are refused as a call out of place. Upgrade: an
// update to a fresh local, then the return or the write.
pub open spec fn spec_stmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e, l) => match e {
            Expr::Call(k, n, args, at) => if spec_callee_writes(all, k) {
                Err(Refusal::Place(at))
            } else {
                match spec_call_lift(k, n, *args, at, all, l, sd) {
                    Ok((c, da)) => Ok(spec_pre(c, DStmt::ReturnCall(k, da))),
                    Err(r) => Err(r),
                }
            },
            _ => match spec_lift(e, all, l, sd, 0, true) {
                Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Return(d))),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match spec_lift(c, all, l, sd, 0, true) {
            Ok((cc, dc, _)) => match spec_stmts(*t, all, env, ps, sd) {
                Ok(dt) => match spec_stmts(*f, all, env, ps, sd) {
                    Ok(df) => Ok(spec_pre(cc, DStmt::If(dc, Box::new(dt), Box::new(df)))),
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
                _ => match spec_lift(e, all, l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, d))),
                    Err(r) => Err(r),
                },
            },
        },
        Stmt::Assign(n, e, l) => if spec_is_mut(ps, n) {
            match spec_lift(e, all, l, sd, 0, true) {
                Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetOut(n, d))),
                Err(r) => Err(r),
            }
        } else if (spec_get(ps, n) is Some) {
            Err(Refusal::WriteParam(n, l))
        } else {
            match e {
                Expr::Call(k, nm, args, at) => if spec_callee_writes(all, k) {
                    Err(Refusal::Place(at))
                } else {
                    match spec_call_lift(k, nm, *args, at, all, l, sd) {
                        Ok((c, da)) => Ok(spec_pre(c, DStmt::AssignCall(n, k, da))),
                        Err(r) => Err(r),
                    }
                },
                _ => match spec_lift(e, all, l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Assign(n, d))),
                    Err(r) => Err(r),
                },
            }
        },
        Stmt::Step(n, t, up, l) => if (spec_get(ps, n) is Some) && !spec_is_mut(ps, n) {
            Err(Refusal::WriteParam(n, l))
        } else {
            match spec_ty(t, l) {
                Err(r) => Err(r),
                Ok(dt) => Ok(spec_step(n, dt, up, spec_is_mut(ps, n))),
            }
        },
        Stmt::While(c, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, env, sd, false) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, env, sd, false) {
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
        Stmt::For(init, c, step, lc, body, l) => match spec_loop_conds(*lc, CondKind::Invariant, spec_scope(*init, env), sd, false) {
            Err(r) => Err(r),
            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, spec_scope(*init, env), sd, false) {
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
        // A range-for is a for loop over the indexes of its sequence parameter, decision 0143. The index is new, the core adds the
        // invariant `i <= v.size()` first, so that the invariants of the author can slice `v[..i]`, and, when the author wrote none,
        // the decreases line `v.size() - i`. Each turn starts with `x = v[i]`.
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match spec_index_of(*lc, fresh) {
            Err(r) => Err(r),
            // An index is new: no variable in scope, and no field of the object, decision 0144.
            Ok((i, il)) => if spec_has(spec_keys(env), i) || spec_this_field(ps, None, i, sd) is Some {
                Err(Refusal::IndexName(i, il))
            } else {
                match seq {
                    Expr::Var(v, Ty::Seq(s, ext)) => if xt != spec_elem(s) {
                        Err(Refusal::Syntax(l))
                    } else {
                        let inner = List::Cons((i, Ty::U64), Box::new(env));
                        match spec_loop_conds(*lc, CondKind::Invariant, inner, sd, true) {
                            Err(r) => Err(r),
                            Ok(inv) => match spec_loop_conds(*lc, CondKind::Decreases, inner, sd, true) {
                                Err(r) => Err(r),
                                Ok(dec) => match spec_contract(spec_range_bound(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd) {
                                    Err(r) => Err(r),
                                    Ok(dbound) => match spec_contract(spec_range_measure(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd) {
                                        Err(r) => Err(r),
                                        Ok(dmeasure) => match spec_code(spec_range_test(i, v, s, ext), l) {
                                            Err(r) => Err(r),
                                            Ok(dc) => match spec_value_ty(xt, l, sd) {
                                                Err(r) => Err(r),
                                                Ok(dt) => match spec_code(spec_range_elem(i, v, s, ext), l) {
                                                    Err(r) => Err(r),
                                                    Ok(de) => match spec_stmts(*body, all, List::Cons((x, xt), Box::new(inner)), ps, sd) {
                                                        Err(r) => Err(r),
                                                        Ok(db) => Ok(DStmt::For(
                                                            Box::new(DStmt::Local(i, DTy::UInt64, spec_range_zero())),
                                                            l,
                                                            dc,
                                                            List::Cons((dbound, l), Box::new(inv)),
                                                            if dec is Nil {
                                                                List::Cons((dmeasure, l), Box::new(List::Nil))
                                                            } else {
                                                                dec
                                                            },
                                                            Box::new(List::Cons((Box::new(DStmt::Local(x, dt, de)), l), Box::new(db))),
                                                            Box::new(spec_step(i, DTy::UInt64, true, false)),
                                                            l,
                                                        )),
                                                    },
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        }
                    },
                    _ => Err(Refusal::Syntax(l)),
                }
            },
        },
        Stmt::SetField(f, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                    Some(_) => match spec_lift(e, all, l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetField(f, d))),
                        Err(r) => Err(r),
                    },
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::SetRefField(p, f, e, l) => match spec_get(ps, p) {
            Some(Ty::Mut(Scalar::Struct(k))) => match spec_field_ty(sd, k, f) {
                Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                Some(_) => match spec_lift(e, all, l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetOutField(p, f, d))),
                    Err(r) => Err(r),
                },
                None => Err(Refusal::NoField(f, l)),
            },
            Some(_) => Err(Refusal::WriteParam(p, l)),
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::Switch(e, k, cs, l) => match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => match spec_cases(*cs, all, env, ps, sd) {
                Ok(dc) => Ok(spec_pre(c, DStmt::Match(d, k, Box::new(dc)))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Call(k, nm, args, l) => spec_call_stmt(k, nm, *args, l, all, ps, sd),
        Stmt::Exit(_) => Ok(DStmt::Exit),
        Stmt::Assert(e, l) => match spec_contract(e, spec_keys(env), spec_after(env), None, List::Nil, l, sd) {
            Ok(d) => Ok(DStmt::Assert(d)),
            Err(r) => Err(r),
        },
        Stmt::Apply(f, args, l) => match spec_contract_args(*args, spec_keys(env), spec_after(env), None, List::Nil, l, sd) {
            Ok(da) => Ok(DStmt::Apply(f, da)),
            Err(r) => Err(r),
        },
        // `v[i] = e` writes one element of a vector by reference, decision 0145. The index and the value hold no call.
        // ponytail: a call in the index or the value is refused as out of place, so the author sets a local first. Upgrade: lift the
        // calls as `Stmt::Assign` does, decision 0104.
        Stmt::SetIndex(v, i, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(_)) => match spec_code(i, l) {
                Ok(di) => match spec_code(e, l) {
                    Ok(de) => Ok(DStmt::SetOut(v, DExpr::SetAt(Box::new(DExpr::Out(v)), Box::new(di), Box::new(de)))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => Err(Refusal::Syntax(l)),
        },
        // `v.push_back(e)` appends one element, decision 0148. A failed push_back throws and never returns to verified code.
        // ponytail: a call in the value is refused as out of place, as for SetIndex. Upgrade: lift the calls, decision 0104.
        Stmt::PushBack(v, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(_)) => match spec_code(e, l) {
                Ok(de) => Ok(DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(de)))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => Err(Refusal::Syntax(l)),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// The cases of a switch, each body over the variables in scope at the switch, decision 0109.
pub open spec fn spec_cases(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DCases, Refusal>
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((i, body), rest) => match spec_stmts(*body, all, env, ps, sd) {
            Ok(db) => match spec_cases(*rest, all, env, ps, sd) {
                Ok(dr) => Ok(List::Cons((i, Box::new(db)), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub open spec fn spec_stmts(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss,
{
    match ss {
        List::Nil => Ok(List::Nil),
        List::Cons(s, rest) => match spec_stmt(*s, all, env, ps, sd) {
            Ok(d) => match spec_stmts(*rest, all, spec_scope(*s, env), ps, sd) {
                Ok(dr) => Ok(List::Cons((Box::new(d), spec_place(*s)), Box::new(dr))),
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
        List::Nil => false,
        List::Cons(a, rest) => spec_has_result(*a) || spec_has_result_args(*rest),
    }
}

/// The lines of one kind of the contract of a function, in their order. A word with no rule, or a line the shell could not read,
/// is refused. A `decreases` line is the measure of a recursion, and it names no `result`, decision 0072. Each kind reads its view
/// of the object, decision 0096.
pub open spec fn spec_conds(cs: Conds, want: CondKind, ps: Params, ret: Ty, sd: Structs) -> Result<DConds, Refusal>
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((k, e, l, decl), rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(w, l)),
            CondKind::Bad(r) => Err(r),
            CondKind::Invariant => Err(Refusal::Misplaced(l)),
            CondKind::Index => Err(Refusal::Misplaced(l)),
            _ => match spec_conds(*rest, want, ps, ret, sd) {
                Ok(dr) => if k == want && k == CondKind::Decreases && spec_has_result(e) {
                    Err(Refusal::Syntax(l))
                } else if k == want {
                    match spec_contract(e, decl, spec_view_ps(ps, k), Some(spec_view_ret(ret, k)), List::Nil, l, sd) {
                        Ok(d) => Ok(List::Cons((d, l), Box::new(dr))),
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
        List::Nil => (None, seen),
        List::Cons((n, _), rest) => if seen.contains(n) {
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
        Stmt::Switch(_, _, cs, _) => spec_twice_cases(seen, *cs),
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
        // The index of a range-for is a name of the function, so a later local cannot take it, decision 0143. An index that is
        // already a name is refused by the translation of the loop, with its own sentence.
        Stmt::RangeFor(fresh, x, _, _, lc, body, l) => {
            let seen1 = match spec_index_of(*lc, fresh) {
                Ok((i, _)) => if seen.contains(i) {
                    seen
                } else {
                    seen.push(i)
                },
                Err(_) => seen,
            };
            if seen1.contains(x) {
                (Some((x, l)), seen1)
            } else {
                spec_twice_stmts(seen1.push(x), *body)
            }
        },
        _ => (None, seen),
    }
}

pub open spec fn spec_twice_stmts(seen: Seq<u32>, ss: Stmts) -> (Option<(u32, u32)>, Seq<u32>)
    decreases ss,
{
    match ss {
        List::Nil => (None, seen),
        List::Cons(s, rest) => {
            let (r, after) = spec_twice_stmt(seen, *s);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_stmts(after, *rest)
            }
        },
    }
}

pub open spec fn spec_twice_cases(seen: Seq<u32>, cs: Cases) -> (Option<(u32, u32)>, Seq<u32>)
    decreases cs,
{
    match cs {
        List::Nil => (None, seen),
        List::Cons((_, body), rest) => {
            let (r, after) = spec_twice_stmts(seen, *body);
            if r.is_some() {
                (r, after)
            } else {
                spec_twice_cases(after, *rest)
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
        List::Nil => None,
        List::Cons(s, rest) => match spec_misreturn_stmt(*s, void) {
            Some(l) => Some(l),
            None => spec_misreturn(*rest, void),
        },
    }
}

pub open spec fn spec_misreturn_cases(cs: Cases, void: bool) -> Option<u32>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => match spec_misreturn(*body, void) {
            Some(l) => Some(l),
            None => spec_misreturn_cases(*rest, void),
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
        Stmt::Switch(_, _, cs, _) => spec_misreturn_cases(*cs, void),
        Stmt::For(init, _, step, _, body, _) => match spec_misreturn_stmt(*init, void) {
            Some(l) => Some(l),
            None => match spec_misreturn_stmt(*step, void) {
                Some(l) => Some(l),
                None => spec_misreturn(*body, void),
            },
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => spec_misreturn(*body, void),
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
                    Ok((req, ens, dec, List::Nil))
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
        List::Nil => tail,
        List::Cons((n, t), rest) => match t {
            Ty::Seq(_, Extent::Fixed(k)) => List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(n)))), Box::new(DExpr::Lit(k))), line), Box::new(spec_bounds(*rest, line, tail))),
            _ => spec_bounds(*rest, line, tail),
        },
    }
}

/// The body of the Dafny function of a member function: the expression of its one `return`, when the function has `this` and its
/// body is that `return` alone, decision 0090. A `return` of a call is a `ReturnCall`, so a pure body holds no call. A function that
/// writes a reference parameter is never pure, decision 0108.
pub open spec fn spec_pure_body(ps: Params, body: DStmts) -> Option<DExpr> {
    match spec_this(ps) {
        Some(_) => if spec_mutates(ps) {
            None
        } else {
            match body {
                List::Cons((s, _), rest) => if *rest == List::Nil {
                    match *s {
                        DStmt::Return(d) => Some(d),
                        _ => None,
                    }
                } else {
                    None
                },
                List::Nil => None,
            }
        },
        None => None,
    }
}

/// The parameters as arguments, each by its name.
pub open spec fn spec_param_args(ps: Params) -> DArgs
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((p, _), rest) => List::Cons(DExpr::Var(p), Box::new(spec_param_args(*rest))),
    }
}

/// The ensures lines of a method, and for a pure member function one more: `result == F(params)`, at the line of the function.
pub open spec fn spec_linked(f: Function, ens: DConds, pure: Option<DExpr>) -> DConds {
    match pure {
        Some(_) => spec_append(
            ens,
            List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(spec_param_args(f.params))))), f.line), Box::new(List::Nil)),
        ),
        None => ens,
    }
}

/// The member `name` of the struct `k`: the key of its function, and its return type when it is pure.
pub open spec fn spec_member(sd: Structs, k: u32, name: u32) -> Option<(u32, Option<(Ty, Params)>)> {
    match spec_get(sd, k) {
        Some((_, _, ms)) => spec_get(ms, name),
        None => None,
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
        List::Nil => None,
        List::Cons(f, rest) => if f.name == key {
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
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((n, (key, spec_pure_ret(all, key, sd, strict))), Box::new(spec_mark_members(*rest, all, sd, strict))),
    }
}

/// The table `t` with each member marked pure or not from the functions of the file, whatever the table said, decision 0090.
/// `sd` is the table that the marks read.
pub open spec fn spec_mark(t: Structs, all: Fns, sd: Structs, strict: bool) -> Structs
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => List::Cons((k, (l, fields, spec_mark_members(ms, all, sd, strict))), Box::new(spec_mark(*rest, all, sd, strict))),
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
        Ty::I8 => Some(DTy::Int8),
        Ty::I16 => Some(DTy::Int16),
        Ty::U16 => Some(DTy::UInt16),
        _ => None,
    }
}

/// The parameters after `this`.
pub open spec fn spec_tail(ps: Params) -> Params {
    match ps {
        List::Cons((_, _), rest) => *rest,
        List::Nil => List::Nil,
    }
}

/// The arguments of a contract call, each exact integer as `(e as T)` for its parameter of type `T`, decision 0095.
pub open spec fn spec_convert(da: DArgs, ps: Params) -> DArgs
    decreases da,
{
    match da {
        List::Nil => List::Nil,
        List::Cons(d, rest) => match ps {
            List::Cons((_, t), prest) => List::Cons(
                match spec_int_dty(t) {
                    Some(dt) => DExpr::Conv(dt, Box::new(d)),
                    None => d,
                },
                Box::new(spec_convert(*rest, *prest))),
            List::Nil => List::Cons(d, Box::new(spec_convert(*rest, List::Nil))),
        },
    }
}

/// The model of a function among the functions `all` of its file, decision 0058.
pub open spec fn spec_function(f: Function, all: Fns, sd: Structs) -> Model {
    match spec_params(f.params, f.line, sd) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match spec_ret_ty(f.ret, f.line, sd) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match spec_modifies(f.params, f.conds, f.line) {
                Some(r) => Model::Refused(r),
                None => match spec_inside(f, all, sd) {
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
                            outs: spec_outs(f.params),
                            trusted: f.trusted,
                        },
                    ),
                },
            },
        },
    }
}

/// The model of a struct: each field a type of the subset, decision 0073. A field can be a sequence, decision 0076.
pub open spec fn spec_fields(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        // An optional of a struct is no field yet, decision 0137.
        List::Cons((n, t), rest) => match (if (t is Opt && t->Opt_0 is Struct) || t is Ptr || t is Own { Err(Refusal::Element(line)) } else { spec_ty(t, line) }) {
            Ok(dt) => match spec_fields(*rest, line) {
                Ok(dr) => Ok(List::Cons((n, dt), Box::new(dr))),
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
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, _)), rest) => List::Cons(
            match spec_fields(fields, l) {
                Ok(df) => Ok((k, df)),
                Err(r) => Err(r),
            },
            Box::new(spec_structs(*rest))),
    }
}

/// The models of the functions `fs`, each among the functions `all` of the file.
pub open spec fn spec_unit(fs: Fns, all: Fns, sd: Structs) -> Models
    decreases fs,
{
    match fs {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(spec_function(*f, all, sd), Box::new(spec_unit(*rest, all, sd))),
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
        Expr::CountIf(a, _, _, t) => unknown_expr(*a) || unknown_expr(*t),
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
        Expr::Shr(a, b, _) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Old(a) => unknown_expr(*a),
        Expr::Cond(c, a, b) => unknown_expr(*c) || unknown_expr(*a) || unknown_expr(*b),
        _ => false,
    }
}

pub open spec fn unknown_args(args: Args) -> bool
    decreases args,
{
    match args {
        List::Nil => false,
        List::Cons(a, rest) => unknown_expr(*a) || unknown_args(*rest),
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
        Stmt::RangeFor(_, _, _, seq, _, body, _) => unknown_expr(seq) || unknown_stmts(*body),
        Stmt::SetField(_, e, _) => unknown_expr(e),
        Stmt::SetRefField(_, _, e, _) => unknown_expr(e),
        Stmt::SetIndex(_, i, e, _) => unknown_expr(i) || unknown_expr(e),
        Stmt::PushBack(_, e, _) => unknown_expr(e),
        Stmt::Switch(e, _, cs, _) => unknown_expr(e) || unknown_cases(*cs),
        Stmt::Call(_, _, args, _) => unknown_args(*args),
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
    }
}

pub open spec fn unknown_cases(cs: Cases) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((_, body), rest) => unknown_stmts(*body) || unknown_cases(*rest),
    }
}

pub open spec fn unknown_stmts(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => unknown_stmt(*s) || unknown_stmts(*rest),
    }
}

pub proof fn lemma_unknown_code_is_refused(e: Expr, line: u32)
    requires
        unknown_expr(e),
    ensures
        spec_code(e, line).is_err(),
{
    lemma_unknown_lift_is_refused(e, List::Nil, line, List::Nil, 0, false);
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
    lemma_unknown_call_lift_is_refused(key, name, args, at, all, line, sd);
}

pub proof fn lemma_unknown_call_stmt_is_refused(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs)
    requires
        unknown_args(args),
    ensures
        spec_call_stmt(key, name, args, line, all, ps, sd).is_err(),
{
    lemma_unknown_call_lift_is_refused(key, name, args, line, all, line, sd);
}

/// A call that stands alone, whose arguments hold a node with no rule, is refused.
pub proof fn lemma_unknown_call_lift_is_refused(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs)
    requires
        unknown_args(args),
    ensures
        spec_call_lift(key, name, args, at, all, line, sd).is_err(),
{
    if spec_callable(all, key, sd) {
        lemma_unknown_lift_args_is_refused(args, all, line, sd, 0, true);
    }
}

/// The value of a return or of a write, with a node with no rule, is refused.
pub proof fn lemma_unknown_value_is_refused(e: Expr, all: Fns, line: u32, sd: Structs)
    requires
        unknown_expr(e),
    ensures
        e is Call ==> spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_err(),
        !(e is Call) ==> spec_lift(e, all, line, sd, 0, true).is_err(),
{
    if e is Call {
        lemma_unknown_call_lift_is_refused(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd);
    } else {
        lemma_unknown_lift_is_refused(e, all, line, sd, 0, true);
    }
}

#[verifier::rlimit(40)]
pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all, env, ps, sd).is_err(),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => lemma_unknown_value_is_refused(e, all, l, sd),
        Stmt::If(c, t, f, l) => {
            if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, true);
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
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            }
        },
        Stmt::SetField(_, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        Stmt::SetRefField(_, _, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        Stmt::SetIndex(_, i, e, l) => {
            if unknown_expr(i) {
                lemma_unknown_code_is_refused(i, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::PushBack(_, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::Switch(e, _, cs, l) => {
            if unknown_expr(e) {
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            } else {
                lemma_unknown_cases_is_refused(*cs, all, env, ps, sd);
            }
        },
        Stmt::Call(k, nm, args, l) => lemma_unknown_call_stmt_is_refused(k, nm, *args, l, all, ps, sd),
        Stmt::Assign(_, e, l) => lemma_unknown_value_is_refused(e, all, l, sd),
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
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => {
            if !unknown_expr(seq) {
                if let Ok((i, _)) = spec_index_of(*lc, fresh) {
                    let turn = List::Cons((x, xt), Box::new(List::Cons((i, Ty::U64), Box::new(env))));
                    lemma_unknown_stmts_is_refused(*body, all, turn, ps, sd);
                }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_cases_is_refused(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_cases(cs),
    ensures
        spec_cases(cs, all, env, ps, sd).is_err(),
    decreases cs,
{
    match cs {
        List::Cons((_, body), rest) => {
            if unknown_stmts(*body) {
                lemma_unknown_stmts_is_refused(*body, all, env, ps, sd);
            } else {
                lemma_unknown_cases_is_refused(*rest, all, env, ps, sd);
            }
        },
        List::Nil => {},
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
        List::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*rest, all, spec_scope(*s, env), ps, sd);
            }
        },
        List::Nil => {},
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
        List::Nil => 0,
        List::Cons(s, rest) => count_stmt(*s) + count_stmts(*rest),
    }
}

pub open spec fn count_stmt(s: Stmt) -> nat
    decreases s,
{
    match s {
        Stmt::If(_, t, f, _) => 1 + count_stmts(*t) + count_stmts(*f),
        Stmt::While(_, _, body, _) => 1 + count_stmts(*body),
        Stmt::Switch(_, _, cs, _) => 1 + count_cases(*cs),
        Stmt::For(init, _, step, _, body, _) => 1 + count_stmt(*init) + count_stmt(*step) + count_stmts(*body),
        // The loop, the start of its index, its step and the element that starts each turn, decision 0143.
        Stmt::RangeFor(_, _, _, _, _, body, _) => 4 + count_stmts(*body),
        _ => 1,
    }
}

pub open spec fn count_cases(cs: Cases) -> nat
    decreases cs,
{
    match cs {
        List::Nil => 0,
        List::Cons((_, body), rest) => count_stmts(*body) + count_cases(*rest),
    }
}

pub open spec fn count_dcases(cs: DCases) -> nat
    decreases cs,
{
    match cs {
        List::Nil => 0,
        List::Cons((_, body), rest) => count_dstmts(*body) + count_dcases(*rest),
    }
}

pub open spec fn count_dstmts(ss: DStmts) -> nat
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons((s, _), rest) => count_dstmt(*s) + count_dstmts(*rest),
    }
}

pub open spec fn count_dstmt(s: DStmt) -> nat
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => 1 + count_dstmts(*t) + count_dstmts(*f),
        DStmt::While(_, _, _, body) => 1 + count_dstmts(*body),
        DStmt::Match(_, _, cs) => 1 + count_dcases(*cs),
        DStmt::For(init, _, _, _, _, body, step, _) => 1 + count_dstmt(*init) + count_dstmt(*step) + count_dstmts(*body),
        DStmt::Pre(_, s) => count_dstmt(*s),
        _ => 1,
    }
}

/// The calls before a statement add no statement.
pub proof fn lemma_pre_count(c: DCalls, s: DStmt)
    ensures
        count_dstmt(spec_pre(c, s)) == count_dstmt(s),
{
}

/// A statement that holds no statement gives one Dafny statement, with or without calls before it.
pub proof fn lemma_kept_return(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Return,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_local(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Local,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_set_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetField || s is SetRefField,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_call(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Call,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}


/// The variables in scope in the body of a range-for: its element, then its index, then those before the loop, decision 0143.
pub open spec fn spec_range_turn(s: Stmt, env: Params) -> Params {
    match s {
        Stmt::RangeFor(fresh, x, xt, _, lc, _, _) => List::Cons(
            (x, xt),
            Box::new(List::Cons((spec_index_of(*lc, fresh).unwrap().0, Ty::U64), Box::new(env))),
        ),
        _ => env,
    }
}

/// A range-for that translates has a body that translates in the scope of its turn.
pub proof fn lemma_range_body_ok(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).is_ok(),
{
}

/// A range-for gives one Dafny statement for the loop, the start of its index, its step and its element, and those of its body.
/// The Dafny loop of a range-for that translates, built from the parts that translate, decision 0143.
pub open spec fn spec_range_dstmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> DStmt {
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let inner = List::Cons((i, Ty::U64), Box::new(env));
                let inv = spec_loop_conds(*lc, CondKind::Invariant, inner, sd, true).unwrap();
                let dec = spec_loop_conds(*lc, CondKind::Decreases, inner, sd, true).unwrap();
                let dbound = spec_contract(spec_range_bound(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd).unwrap();
                let dmeasure = spec_contract(spec_range_measure(i, v), spec_keys(inner), spec_after(inner), None, List::Nil, l, sd).unwrap();
                let dc = spec_code(spec_range_test(i, v, sc, ext), l).unwrap();
                let dt = spec_value_ty(xt, l, sd).unwrap();
                let de = spec_code(spec_range_elem(i, v, sc, ext), l).unwrap();
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                DStmt::For(
                    Box::new(DStmt::Local(i, DTy::UInt64, spec_range_zero())),
                    l,
                    dc,
                    List::Cons((dbound, l), Box::new(inv)),
                    if dec is Nil {
                        List::Cons((dmeasure, l), Box::new(List::Nil))
                    } else {
                        dec
                    },
                    Box::new(List::Cons((Box::new(DStmt::Local(x, dt, de)), l), Box::new(db))),
                    Box::new(spec_step(i, DTy::UInt64, true, false)),
                    l,
                )
            },
            _ => DStmt::Exit,
        },
        _ => DStmt::Exit,
    }
}

/// A range-for that translates gives the loop of spec_range_dstmt.
#[verifier::rlimit(60)]
pub proof fn lemma_range_shape(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        spec_stmt(s, all, env, ps, sd).unwrap() == spec_range_dstmt(s, all, env, ps, sd),
{
}

/// A range-for gives one Dafny statement for the loop, the start of its index, its step and its element, and those of its body.
pub proof fn lemma_range_kept(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        count_dstmts(spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).unwrap()) == count_stmts(*s->RangeFor_5),
    ensures
        count_dstmt(spec_range_dstmt(s, all, env, ps, sd)) == count_stmt(s),
{
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                let first = DStmt::Local(x, spec_value_ty(xt, l, sd).unwrap(), spec_code(spec_range_elem(i, v, sc, ext), l).unwrap());
                let b: DStmts = List::Cons((Box::new(first), l), Box::new(db));
                assert(count_dstmt(first) == 1);
                assert(count_dstmts(b) == count_dstmt(first) + count_dstmts(db));
                assert(count_dstmt(DStmt::Local(i, DTy::UInt64, spec_range_zero())) == 1);
                assert(count_dstmt(spec_step(i, DTy::UInt64, true, false)) == 1);
                assert(count_stmt(s) == 4 + count_stmts(*body));
            },
            _ => {},
        },
        _ => {},
    }
}

/// The calls of a range-for are those of its body.
pub proof fn lemma_range_resolves(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        s is RangeFor,
        s->RangeFor_3 is Var,
        s->RangeFor_3->Var_1 is Seq,
        calls_resolve(spec_stmts(*s->RangeFor_5, all, spec_range_turn(s, env), ps, sd).unwrap(), all, sd),
    ensures
        calls_resolve_stmt(spec_range_dstmt(s, all, env, ps, sd), all, sd),
{
    match s {
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match seq {
            Expr::Var(v, Ty::Seq(sc, ext)) => {
                let i = spec_index_of(*lc, fresh).unwrap().0;
                let db = spec_stmts(*body, all, spec_range_turn(s, env), ps, sd).unwrap();
                let first = DStmt::Local(x, spec_value_ty(xt, l, sd).unwrap(), spec_code(spec_range_elem(i, v, sc, ext), l).unwrap());
                let b: DStmts = List::Cons((Box::new(first), l), Box::new(db));
                assert(calls_resolve_stmt(first, all, sd));
                assert(calls_resolve(b, all, sd));
                assert(calls_resolve_stmt(DStmt::Local(i, DTy::UInt64, spec_range_zero()), all, sd));
                assert(calls_resolve_stmt(spec_step(i, DTy::UInt64, true, false), all, sd));
            },
            _ => {},
        },
        _ => {},
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
        Stmt::Return(_, _) => lemma_kept_return(s, all, env, ps, sd),
        Stmt::Local(_, _, _, _) => lemma_kept_local(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_kept_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::Switch(e, k, cs, l) => {
            lemma_cases_kept(*cs, all, env, ps, sd);
            let ce = spec_lift(e, all, l, sd, 0, true).unwrap();
            lemma_pre_count(ce.0, DStmt::Match(ce.1, k, Box::new(spec_cases(*cs, all, env, ps, sd).unwrap())));
        },
        Stmt::Call(_, _, _, _) => lemma_kept_call(s, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            lemma_statements_kept(*t, all, env, ps, sd);
            lemma_statements_kept(*f, all, env, ps, sd);
            let cc = spec_lift(c, all, l, sd, 0, true).unwrap();
            let body = DStmt::If(cc.1, Box::new(spec_stmts(*t, all, env, ps, sd).unwrap()), Box::new(spec_stmts(*f, all, env, ps, sd).unwrap()));
            lemma_pre_count(cc.0, body);
        },
        Stmt::While(_, _, body, _) => {
            lemma_statements_kept(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_kept(*init, all, env, ps, sd);
            lemma_stmt_kept(*step, all, spec_scope(*init, env), ps, sd);
            lemma_statements_kept(*body, all, spec_scope(*init, env), ps, sd);
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => {
            lemma_range_body_ok(s, all, env, ps, sd);
            lemma_range_shape(s, all, env, ps, sd);
            lemma_statements_kept(*body, all, spec_range_turn(s, env), ps, sd);
            lemma_range_kept(s, all, env, ps, sd);
        },
        _ => {},
    }
}

/// A translated body has one Dafny statement for each C++ statement, branches and loops included.
pub proof fn lemma_cases_kept(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_cases(cs, all, env, ps, sd).is_ok(),
    ensures
        count_dcases(spec_cases(cs, all, env, ps, sd).unwrap()) == count_cases(cs),
    decreases cs,
{
    match cs {
        List::Cons((_, body), rest) => {
            lemma_statements_kept(*body, all, env, ps, sd);
            lemma_cases_kept(*rest, all, env, ps, sd);
        },
        List::Nil => {},
    }
}

pub proof fn lemma_statements_kept(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts(ss, all, env, ps, sd).is_ok(),
    ensures
        count_dstmts(spec_stmts(ss, all, env, ps, sd).unwrap()) == count_stmts(ss),
    decreases ss,
{
    match ss {
        List::Cons(s, rest) => {
            lemma_stmt_kept(*s, all, env, ps, sd);
            lemma_statements_kept(*rest, all, spec_scope(*s, env), ps, sd);
        },
        List::Nil => {},
    }
}

/// The models hold a method, full or bare, with this key.
pub open spec fn has_method(ms: Models, key: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons(m, rest) => match m {
            Model::Full(method) => method.name == key || has_method(*rest, key),
            Model::Bare(name, _, _, _) => name == key || has_method(*rest, key),
            Model::Refused(_) => has_method(*rest, key),
        },
    }
}

/// Each call of the statements names a key of `all` that has a method.
pub open spec fn calls_resolve_cases(cs: DCases, all: Fns, sd: Structs) -> bool
    decreases cs,
{
    match cs {
        List::Nil => true,
        List::Cons((_, body), rest) => calls_resolve(*body, all, sd) && calls_resolve_cases(*rest, all, sd),
    }
}

pub open spec fn calls_resolve(ss: DStmts, all: Fns, sd: Structs) -> bool
    decreases ss,
{
    match ss {
        List::Nil => true,
        List::Cons((s, _), rest) => calls_resolve_stmt(*s, all, sd) && calls_resolve(*rest, all, sd),
    }
}

pub open spec fn calls_resolve_stmt(s: DStmt, all: Fns, sd: Structs) -> bool
    decreases s,
{
    match s {
        DStmt::If(_, t, f) => calls_resolve(*t, all, sd) && calls_resolve(*f, all, sd),
        DStmt::Match(_, _, cs) => calls_resolve_cases(*cs, all, sd),
        DStmt::LocalCall(_, _, k, _) => spec_callable(all, k, sd),
        DStmt::ReturnCall(k, _) => spec_callable(all, k, sd),
        DStmt::AssignCall(_, k, _) => spec_callable(all, k, sd),
        DStmt::Update(_, k, _) => spec_callable(all, k, sd),
        DStmt::LocalUpdate(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::CallStmt(k, _) => spec_callable(all, k, sd),
        DStmt::Pre(c, s) => calls_resolve_calls(c, all, sd) && calls_resolve_stmt(*s, all, sd),
        DStmt::While(_, _, _, body) => calls_resolve(*body, all, sd),
        DStmt::For(init, _, _, _, _, body, step, _) => calls_resolve_stmt(*init, all, sd) && calls_resolve(*body, all, sd) && calls_resolve_stmt(*step, all, sd),
        _ => true,
    }
}

/// Each call that runs before a statement names a key of `all` that has a method.
pub open spec fn calls_resolve_calls(c: DCalls, all: Fns, sd: Structs) -> bool
    decreases c,
{
    match c {
        List::Nil => true,
        List::Cons((_, _, k, _), rest) => spec_callable(all, k, sd) && calls_resolve_calls(*rest, all, sd),
    }
}

pub proof fn lemma_append_resolves(a: DCalls, b: DCalls, all: Fns, sd: Structs)
    ensures
        calls_resolve_calls(spec_append(a, b), all, sd) == (calls_resolve_calls(a, all, sd) && calls_resolve_calls(b, all, sd)),
    decreases a,
{
    match a {
        List::Cons((_, _, _, _), rest) => lemma_append_resolves(*rest, b, all, sd),
        List::Nil => {},
    }
}

/// Each call that a lifted expression runs first names a key that has a method.
#[verifier::rlimit(60)]
pub proof fn lemma_lift_resolves(e: Expr, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        spec_lift(e, all, line, sd, n, open).is_ok(),
    ensures
        calls_resolve_calls(spec_lift(e, all, line, sd, n, open).unwrap().0, all, sd),
    decreases e,
{
    match e {
        Expr::Call(k, _, args, _) => {
            lemma_lift_args_resolves(*args, all, line, sd, n, open);
            let (ca, da, n1) = spec_lift_args(*args, all, line, sd, n, open).unwrap();
            let dt = spec_callee_ty(all, k, line, sd).unwrap();
            assert(spec_callable(all, k, sd));
            assert(calls_resolve_calls(List::Nil, all, sd));
            assert(calls_resolve_calls(List::Cons((n1, dt, k, da), Box::new(List::Nil)), all, sd));
            lemma_append_resolves(ca, List::Cons((n1, dt, k, da), Box::new(List::Nil)), all, sd);
        },
        Expr::Bin(op, a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let (ca, _, n1) = spec_lift(*a, all, line, sd, n, open).unwrap();
            let ob = open && !(op == BinOp::And || op == BinOp::Or);
            lemma_lift_resolves(*b, all, line, sd, n1, ob);
            lemma_append_resolves(ca, spec_lift(*b, all, line, sd, n1, ob).unwrap().0, all, sd);
        },
        Expr::Divide(_, a, b, _) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Shr(a, b, _) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Index(a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Subspan(a, b) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_resolves(*b, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift(*b, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        Expr::Not(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Neg(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Cast(_, a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Paren(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Brace(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Size(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Copy(a, _, _) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Field(a, _) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::HasValue(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Value(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Wrap(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Empty(a) => lemma_lift_resolves(*a, all, line, sd, n, open),
        Expr::Construct(_, args) => lemma_lift_args_resolves(*args, all, line, sd, n, open),
        Expr::Cond(c, a, b) => {
            lemma_lift_resolves(*c, all, line, sd, n, open);
            let (cc, _, n1) = spec_lift(*c, all, line, sd, n, open).unwrap();
            lemma_lift_resolves(*a, all, line, sd, n1, false);
            let (ca, _, n2) = spec_lift(*a, all, line, sd, n1, false).unwrap();
            lemma_lift_resolves(*b, all, line, sd, n2, false);
            let cb = spec_lift(*b, all, line, sd, n2, false).unwrap().0;
            lemma_append_resolves(ca, cb, all, sd);
            lemma_append_resolves(cc, spec_append(ca, cb), all, sd);
        },
        _ => {},
    }
}

pub proof fn lemma_lift_args_resolves(args: Args, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        spec_lift_args(args, all, line, sd, n, open).is_ok(),
    ensures
        calls_resolve_calls(spec_lift_args(args, all, line, sd, n, open).unwrap().0, all, sd),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_lift_resolves(*a, all, line, sd, n, open);
            let n1 = spec_lift(*a, all, line, sd, n, open).unwrap().2;
            lemma_lift_args_resolves(*rest, all, line, sd, n1, open);
            lemma_append_resolves(spec_lift(*a, all, line, sd, n, open).unwrap().0, spec_lift_args(*rest, all, line, sd, n1, open).unwrap().0, all, sd);
        },
        List::Nil => {},
    }
}

/// An expression that holds a node with no rule is refused.
pub proof fn lemma_unknown_lift_is_refused(e: Expr, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        unknown_expr(e),
    ensures
        spec_lift(e, all, line, sd, n, open).is_err(),
    decreases e,
{
    match e {
        Expr::Call(_, _, args, _) => lemma_unknown_lift_args_is_refused(*args, all, line, sd, n, open),
        Expr::Bin(op, a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open && !(op == BinOp::And || op == BinOp::Or));
            }
        },
        Expr::Divide(_, a, b, _) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Shr(a, b, _) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        // The sequence of a count is a variable, so a node with no rule is in the test, which lifts with no call.
        Expr::CountIf(a, _, _, t) => {
            if unknown_expr(*t) {
                lemma_unknown_lift_is_refused(*t, List::Nil, line, List::Nil, 0, false);
            } else {
                assert(!(*a is Var)) by {
                    if *a is Var {
                        assert(!unknown_expr(*a));
                    }
                }
            }
        },
        Expr::Index(a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Subspan(a, b) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        Expr::Not(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Neg(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Cast(_, a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Paren(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Brace(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Size(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Copy(a, _, _) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Field(a, _) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::HasValue(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Value(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Wrap(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Empty(a) => lemma_unknown_lift_is_refused(*a, all, line, sd, n, open),
        Expr::Construct(_, args) => lemma_unknown_lift_args_is_refused(*args, all, line, sd, n, open),
        Expr::Cond(c, a, b) => {
            if unknown_expr(*c) {
                lemma_unknown_lift_is_refused(*c, all, line, sd, n, open);
            } else if spec_lift(*c, all, line, sd, n, open).is_ok() {
                {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false);
            } else if spec_lift(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false).is_ok() {
                lemma_unknown_lift_is_refused(*b, all, line, sd, spec_lift(*a, all, line, sd, spec_lift(*c, all, line, sd, n, open).unwrap().2, false).unwrap().2, false);
            }
        }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_unknown_lift_args_is_refused(args: Args, all: Fns, line: u32, sd: Structs, n: u32, open: bool)
    requires
        unknown_args(args),
    ensures
        spec_lift_args(args, all, line, sd, n, open).is_err(),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            if unknown_expr(*a) {
                lemma_unknown_lift_is_refused(*a, all, line, sd, n, open);
            } else if spec_lift(*a, all, line, sd, n, open).is_ok() {
                lemma_unknown_lift_args_is_refused(*rest, all, line, sd, spec_lift(*a, all, line, sd, n, open).unwrap().2, open);
            }
        },
        List::Nil => {},
    }
}

/// A lift where a call has no place runs no call, so a loop condition drops none.
pub proof fn lemma_closed_runs_no_call(e: Expr, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lift(e, all, line, sd, n, false).is_ok(),
    ensures
        spec_lift(e, all, line, sd, n, false).unwrap().0 == List::Nil,
    decreases e,
{
    match e {
        Expr::Bin(_, a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Divide(_, a, b, _) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Shr(a, b, _) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Index(a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Subspan(a, b) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        Expr::Not(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Neg(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Cast(_, a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Paren(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Brace(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Size(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Copy(a, _, _) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Field(a, _) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::HasValue(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Value(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Wrap(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Empty(a) => lemma_closed_runs_no_call(*a, all, line, sd, n),
        Expr::Construct(_, args) => lemma_closed_args_run_no_call(*args, all, line, sd, n),
        Expr::Cond(c, a, b) => {
            lemma_closed_runs_no_call(*c, all, line, sd, n);
            let n1 = spec_lift(*c, all, line, sd, n, false).unwrap().2;
            lemma_closed_runs_no_call(*a, all, line, sd, n1);
            lemma_closed_runs_no_call(*b, all, line, sd, spec_lift(*a, all, line, sd, n1, false).unwrap().2);
        },
        _ => {},
    }
}

pub proof fn lemma_closed_args_run_no_call(args: Args, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lift_args(args, all, line, sd, n, false).is_ok(),
    ensures
        spec_lift_args(args, all, line, sd, n, false).unwrap().0 == List::Nil,
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_closed_runs_no_call(*a, all, line, sd, n);
            lemma_closed_args_run_no_call(*rest, all, line, sd, spec_lift(*a, all, line, sd, n, false).unwrap().2);
        },
        List::Nil => {},
    }
}

/// The calls before a statement resolve when each of them names a key with a method.
pub proof fn lemma_pre_resolves(c: DCalls, s: DStmt, all: Fns, sd: Structs)
    ensures
        calls_resolve_stmt(spec_pre(c, s), all, sd) == (calls_resolve_calls(c, all, sd) && calls_resolve_stmt(s, all, sd)),
{
}

/// A call that stands alone names a key with a method, and so does each call in its arguments.
pub proof fn lemma_call_lift_resolves(key: u32, name: u32, args: Args, at: u32, all: Fns, line: u32, sd: Structs)
    requires
        spec_call_lift(key, name, args, at, all, line, sd).is_ok(),
    ensures
        spec_callable(all, key, sd),
        calls_resolve_calls(spec_call_lift(key, name, args, at, all, line, sd).unwrap().0, all, sd),
{
    lemma_lift_args_resolves(args, all, line, sd, 0, true);
}

/// The value of a return or of a write resolves its calls.
pub proof fn lemma_value_resolves(e: Expr, all: Fns, line: u32, sd: Structs)
    ensures
        (e is Call && spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_ok()) ==> spec_callable(all, e->Call_0, sd)
            && calls_resolve_calls(spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).unwrap().0, all, sd),
        (!(e is Call) && spec_lift(e, all, line, sd, 0, true).is_ok()) ==> calls_resolve_calls(spec_lift(e, all, line, sd, 0, true).unwrap().0, all, sd),
{
    if e is Call {
        if spec_call_lift(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd).is_ok() {
            lemma_call_lift_resolves(e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, line, sd);
        }
    } else if spec_lift(e, all, line, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, line, sd, 0, true);
    }
}

pub proof fn lemma_resolves_return(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Return,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    lemma_value_resolves(s->Return_0, all, s->Return_1, sd);
}

pub proof fn lemma_resolves_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->Assign_1;
    let l = s->Assign_2;
    if spec_is_mut(ps, s->Assign_0) {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOut(s->Assign_0, d), all, sd);
    } else {
        lemma_value_resolves(e, all, l, sd);
    }
}

pub proof fn lemma_resolves_set_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->SetField_1;
    let l = s->SetField_2;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetField(s->SetField_0, d), all, sd);
    }
}

pub proof fn lemma_resolves_set_ref_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetRefField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->SetRefField_2;
    let l = s->SetRefField_3;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOutField(s->SetRefField_0, s->SetRefField_1, d), all, sd);
    }
}

/// A statement that holds no call gives a Dafny statement that holds none.
pub proof fn lemma_resolves_plain(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Step || s is Exit || s is Assert || s is Apply || s is Unknown || s is SetIndex || s is PushBack,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
}

pub proof fn lemma_resolves_local(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Local,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let e = s->Local_2;
    let l = s->Local_3;
    lemma_value_resolves(e, all, l, sd);
    if let Expr::Call(k, nm, args, at) = e {
        if let List::Cons(_, rest) = *args {
            if spec_call_lift(k, nm, *rest, at, all, l, sd).is_ok() {
                lemma_call_lift_resolves(k, nm, *rest, at, all, l, sd);
            }
        }
    }
}

pub proof fn lemma_resolves_call(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Call,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let k = s->Call_0;
    let nm = s->Call_1;
    let args = *s->Call_2;
    let l = s->Call_3;
    if spec_call_lift(k, nm, args, l, all, l, sd).is_ok() {
        lemma_call_lift_resolves(k, nm, args, l, all, l, sd);
    }
    if let List::Cons(_, rest) = args {
        if spec_call_lift(k, nm, *rest, l, all, l, sd).is_ok() {
            lemma_call_lift_resolves(k, nm, *rest, l, all, l, sd);
        }
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
        Stmt::Return(_, _) => lemma_resolves_return(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_resolves_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_resolves_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_resolves_set_ref_field(s, all, env, ps, sd),
        Stmt::Switch(e, k, cs, l) => {
            lemma_cases_calls_resolve(*cs, all, env, ps, sd);
            lemma_lift_resolves(e, all, l, sd, 0, true);
            let (ce, de, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
            lemma_pre_resolves(ce, DStmt::Match(de, k, Box::new(spec_cases(*cs, all, env, ps, sd).unwrap())), all, sd);
        },
        Stmt::Local(_, _, _, _) => lemma_resolves_local(s, all, env, ps, sd),
        Stmt::Call(_, _, _, _) => lemma_resolves_call(s, all, env, ps, sd),
        Stmt::Step(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Exit(_) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Assert(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Apply(_, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Unknown(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetIndex(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::PushBack(_, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            lemma_stmts_calls_resolve(*t, all, env, ps, sd);
            lemma_stmts_calls_resolve(*f, all, env, ps, sd);
            lemma_lift_resolves(c, all, l, sd, 0, true);
            let (cc, dc, _) = spec_lift(c, all, l, sd, 0, true).unwrap();
            let body = DStmt::If(dc, Box::new(spec_stmts(*t, all, env, ps, sd).unwrap()), Box::new(spec_stmts(*f, all, env, ps, sd).unwrap()));
            lemma_pre_resolves(cc, body, all, sd);
        },
        Stmt::While(_, _, body, _) => {
            lemma_stmts_calls_resolve(*body, all, env, ps, sd);
        },
        Stmt::For(init, _, step, _, body, _) => {
            lemma_stmt_calls_resolve(*init, all, env, ps, sd);
            lemma_stmt_calls_resolve(*step, all, spec_scope(*init, env), ps, sd);
            lemma_stmts_calls_resolve(*body, all, spec_scope(*init, env), ps, sd);
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => {
            lemma_range_body_ok(s, all, env, ps, sd);
            lemma_range_shape(s, all, env, ps, sd);
            lemma_stmts_calls_resolve(*body, all, spec_range_turn(s, env), ps, sd);
            lemma_range_resolves(s, all, env, ps, sd);
        },
    }
}

pub proof fn lemma_cases_calls_resolve(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_cases(cs, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_cases(spec_cases(cs, all, env, ps, sd).unwrap(), all, sd),
    decreases cs,
{
    match cs {
        List::Cons((_, body), rest) => {
            lemma_stmts_calls_resolve(*body, all, env, ps, sd);
            lemma_cases_calls_resolve(*rest, all, env, ps, sd);
        },
        List::Nil => {},
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
        List::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all, env, ps, sd);
            lemma_stmts_calls_resolve(*rest, all, spec_scope(*s, env), ps, sd);
        },
        List::Nil => {},
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
        List::Cons(f, rest) => {
            if !(f.name == key && has_signature(*f, sd)) {
                lemma_callable_has_method(*rest, all, key, sd);
            }
        },
        List::Nil => {},
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

pub fn scalar_dty(s: Scalar) -> (r: DTy)
    ensures
        r == spec_scalar_dty(s),
{
    match s {
        Scalar::I32 => DTy::Int32,
        Scalar::I64 => DTy::Int64,
        Scalar::U8 => DTy::UInt8,
        Scalar::U32 => DTy::UInt32,
        Scalar::U64 => DTy::UInt64,
        Scalar::Bool => DTy::Bool,
        Scalar::Struct(k) => DTy::Struct(k),
    }
}

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
        Ty::I8 => Ok(DTy::Int8),
        Ty::I16 => Ok(DTy::Int16),
        Ty::U16 => Ok(DTy::UInt16),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        Ty::Opt(s) => Ok(DTy::Opt(s)),
        // A pointer to const is an Option in Dafny, decisions 0140 and 0141.
        Ty::Ptr(s) => Ok(DTy::Opt(s)),
        // A unique_ptr is an Option in Dafny too, decision 0142.
        Ty::Own(s) => Ok(DTy::Opt(s)),
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::ThisMut(k) => Ok(DTy::Struct(k)),
        Ty::ThisAfter(k) => Ok(DTy::Struct(k)),
        Ty::Mut(s) => Ok(scalar_dty(s)),
        Ty::MutAfter(s) => Ok(scalar_dty(s)),
        Ty::MutSeq(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::MutSeqAfter(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::MutSeq(s) => Ok(DTy::Seq(s)),
        Ty::MutSeqAfter(s) => Ok(DTy::Seq(s)),
        Ty::Enum(k) => Ok(DTy::Enum(k)),
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
            Ty::Mut(_) => Err(Refusal::Syntax(line)),
            Ty::MutAfter(_) => Err(Refusal::Syntax(line)),
            Ty::MutSeq(_) => Err(Refusal::Syntax(line)),
            Ty::MutSeqAfter(_) => Err(Refusal::Syntax(line)),
            Ty::Ptr(_) => Err(Refusal::Syntax(line)),
            Ty::Struct(k) => if holds_seq(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            Ty::Opt(Scalar::Struct(k)) => if holds_seq(sd, k) {
                Err(Refusal::HoldsSeq(line))
            } else {
                Ok(dt)
            },
            Ty::Own(Scalar::Struct(k)) => if holds_seq(sd, k) {
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
{
    match get_ref(sd, k) {
        Some((_, fields, _)) => Some(fields),
        None => None,
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
        List::Nil => false,
        List::Cons((_, t), rest) => {
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
        (Ty::Ptr(a), Ty::Ptr(b)) => a == b,
        (Ty::Own(a), Ty::Own(b)) => a == b,
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
{
    match lift(e, &List::Nil, line, &List::Nil, 0, false) {
        Ok((_, d, _)) => Ok(d),
        Err(r) => Err(r),
    }
}

pub fn pre(c: DCalls, s: DStmt) -> (r: DStmt)
    ensures
        r == spec_pre(c, s),
{
    match c {
        List::Nil => s,
        _ => DStmt::Pre(c, Box::new(s)),
    }
}

pub fn callee_ty(all: &Fns, key: u32, line: u32, sd: &Structs) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_callee_ty(*all, key, line, *sd),
{
    match find(all, key) {
        Some(f) => match f.ret {
            Ty::This(_) => ret_ty(f.ret, line, sd),
            _ => translate_value_ty(f.ret, line, sd),
        },
        None => Err(Refusal::Syntax(line)),
    }
}

pub fn lift(e: &Expr, all: &Fns, line: u32, sd: &Structs, n: u32, open: bool) -> (r: Result<(DCalls, DExpr, u32), Refusal>)
    ensures
        r == spec_lift(*e, *all, line, *sd, n, open),
    decreases e,
{
    match e {
        Expr::Lit(v, t) => match translate_ty(*t, line) {
            Ok(dt) => Ok((List::Nil, DExpr::Conv(dt, Box::new(DExpr::Lit(*v))), n)),
            Err(r) => Err(r),
        },
        Expr::Bool(v) => Ok((List::Nil, DExpr::Bool(*v), n)),
        Expr::Enumerator(k, i) => Ok((List::Nil, DExpr::Enumerator(*k, *i), n)),
        Expr::Var(v, t) => match translate_ty(*t, line) {
            Ok(_) => Ok((List::Nil, code_var(*v, *t), n)),
            Err(r) => Err(r),
        },
        Expr::Call(k, nm, args, at) => if !open || callee_writes(all, *k) {
            Err(Refusal::Place(*at))
        } else if !callable(all, *k, sd) {
            Err(Refusal::Callee(*nm, *at))
        } else {
            match lift_args(args, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match callee_ty(all, *k, line, sd) {
                    Err(r) => Err(r),
                    Ok(dt) => if n1 < 0xFFFF_FFFF {
                        Ok((append(ca, List::Cons((n1, dt, *k, da), Box::new(List::Nil))), DExpr::Temp(n1), n1 + 1))
                    } else {
                        Err(Refusal::Syntax(line))
                    },
                },
            }
        },
        Expr::Bin(op, a, b) if (*op == BinOp::Eq || *op == BinOp::Ne) && (a.is_nullopt() || b.is_nullopt()) => if b.is_nullopt() {
            match lift(a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => Ok((ca, null_test(*op, da), n1)),
            }
        } else {
            match lift(b, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((cb, db, n1)) => Ok((cb, null_test(*op, db), n1)),
            }
        },
        Expr::Bin(op, a, b) => if *op == BinOp::Div || *op == BinOp::Rem || a.is_ptr_var() || b.is_ptr_var() {
            Err(Refusal::Syntax(line))
        } else {
            match lift(a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open && !(*op == BinOp::And || *op == BinOp::Or)) {
                    Err(r) => Err(r),
                    Ok((cb, db, n2)) => Ok((append(ca, cb), DExpr::Bin(*op, Box::new(da), Box::new(db)), n2)),
                },
            }
        },
        Expr::Divide(op, a, b, t) => if !(*op == BinOp::Div || *op == BinOp::Rem) {
            Err(Refusal::Syntax(line))
        } else {
            match lift(a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open) {
                    Err(r) => Err(r),
                    Ok((cb, db, n2)) => match divide(*op, da, db, *t, line) {
                        Err(r) => Err(r),
                        Ok(d) => Ok((append(ca, cb), d, n2)),
                    },
                },
            }
        },
        Expr::Shr(a, b, t) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cb, db, n2)) => match shift(da, db, *t, line) {
                    Err(r) => Err(r),
                    Ok(d) => Ok((append(ca, cb), d, n2)),
                },
            },
        },
        Expr::Not(a) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Not(Box::new(d)), n1)),
        },
        Expr::Neg(a) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Neg(Box::new(d)), n1)),
        },
        Expr::Cast(ck, a) => match ck {
            CastKind::Other(k) => Err(Refusal::Construct(*k, line)),
            CastKind::Integral(from, to) => match lift(a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((c, d, n1)) => match translate_integral(*from, *to, d, line) {
                    Err(r) => Err(r),
                    Ok(di) => Ok((c, di, n1)),
                },
            },
            _ => lift(a, all, line, sd, n, open),
        },
        Expr::Paren(a) => lift(a, all, line, sd, n, open),
        Expr::Brace(a) => lift(a, all, line, sd, n, open),
        Expr::Size(o) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Conv(DTy::UInt64, Box::new(DExpr::Len(Box::new(d)))), n1)),
        },
        Expr::CountIf(o, x, xt, t) => match &**o {
            Expr::Var(v, vt) => match seq_elem(*vt) {
                Some(s) => if elem(s) == *xt {
                    match translate_ty(*xt, line) {
                        Err(r) => Err(r),
                        Ok(dx) => match lift(t, &List::Nil, line, &List::Nil, 0, false) {
                            Err(r) => Err(r),
                            Ok((_, dt, _)) => Ok((List::Nil, DExpr::Conv(DTy::Int64, Box::new(DExpr::CountIf(Box::new(code_var(*v, *vt)), *x, dx, Box::new(dt)))), n)),
                        },
                    }
                } else {
                    Err(Refusal::Syntax(line))
                },
                None => Err(Refusal::Syntax(line)),
            },
            _ => Err(Refusal::Syntax(line)),
        },
        Expr::Index(o, i) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((co, d, n1)) => match lift(i, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((ci, di, n2)) => Ok((append(co, ci), DExpr::Index(Box::new(d), Box::new(di)), n2)),
            },
        },
        Expr::Copy(a, from, to) => if copy_ok(*from, *to) {
            lift(a, all, line, sd, n, open)
        } else {
            Err(Refusal::Extent(line))
        },
        Expr::Field(o, f) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Field(Box::new(d), *f), n1)),
        },
        Expr::Construct(k, args) => match lift_args(args, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, da, n1)) => Ok((c, DExpr::Ctor(*k, Box::new(da)), n1)),
        },
        Expr::HasValue(o) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::IsSome(Box::new(d)), n1)),
        },
        Expr::Value(o) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Get(Box::new(d)), n1)),
        },
        Expr::Nullopt => Ok((List::Nil, DExpr::Nothing, n)),
        Expr::Wrap(a) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Just(Box::new(d)), n1)),
        },
        Expr::Empty(o) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0))), n1)),
        },
        Expr::Subspan(o, k) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((co, d, n1)) => match lift(k, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((ck, dk, n2)) => Ok((append(co, ck), DExpr::Drop(Box::new(d), Box::new(dk)), n2)),
            },
        },
        Expr::Cond(cnd, a, b) => match lift(cnd, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, dc, n1)) => match lift(a, all, line, sd, n1, false) {
                Err(r) => Err(r),
                Ok((ca, da, n2)) => match lift(b, all, line, sd, n2, false) {
                    Err(r) => Err(r),
                    Ok((cb, db, n3)) => Ok((append(c, append(ca, cb)), DExpr::Ite(Box::new(dc), Box::new(da), Box::new(db)), n3)),
                },
            },
        },
        Expr::Name(v) => Err(Refusal::Name(*v, line)),
        Expr::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
        _ => Err(Refusal::Syntax(line)),
    }
}

pub fn lift_args(args: &Args, all: &Fns, line: u32, sd: &Structs, n: u32, open: bool) -> (r: Result<(DCalls, DArgs, u32), Refusal>)
    ensures
        r == spec_lift_args(*args, *all, line, *sd, n, open),
    decreases args,
{
    match args {
        List::Nil => Ok((List::Nil, List::Nil, n)),
        List::Cons(a, rest) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match lift_args(rest, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cr, dr, n2)) => Ok((append(ca, cr), List::Cons(da, Box::new(dr)), n2)),
            },
        },
    }
}

pub fn call_lift(key: u32, name: u32, args: &Args, at: u32, all: &Fns, line: u32, sd: &Structs) -> (r: Result<(DCalls, DArgs), Refusal>)
    ensures
        r == spec_call_lift(key, name, *args, at, *all, line, *sd),
{
    if callable(all, key, sd) {
        match lift_args(args, all, line, sd, 0, true) {
            Ok((c, da, _)) => Ok((c, da)),
            Err(r) => Err(r),
        }
    } else {
        Err(Refusal::Callee(name, at))
    }
}

pub fn code_var(v: u32, t: Ty) -> (r: DExpr)
    ensures
        r == spec_code_var(v, t),
{
    match t {
        Ty::ThisMut(_) => DExpr::After,
        Ty::Mut(_) => DExpr::Out(v),
        Ty::MutSeq(_) => DExpr::Out(v),
        _ => DExpr::Var(v),
    }
}

pub fn contract_var(v: u32, t: Ty) -> (r: DExpr)
    ensures
        r == spec_var(v, t),
{
    match t {
        Ty::ThisAfter(_) => DExpr::After,
        Ty::MutAfter(_) => DExpr::Out(v),
        Ty::MutSeqAfter(_) => DExpr::Out(v),
        _ => DExpr::Var(v),
    }
}

pub fn view_ty(t: Ty) -> (r: Ty)
    ensures
        r == spec_view_ty(t),
{
    match t {
        Ty::Mut(s) => elem(s),
        Ty::MutAfter(s) => elem(s),
        Ty::MutSeq(s) => Ty::Seq(s, Extent::Dynamic),
        Ty::MutSeqAfter(s) => Ty::Seq(s, Extent::Dynamic),
        _ => t,
    }
}

pub fn rebind(decl: &Names, ps: &Params, name: u32) -> (r: Option<(u32, Ty)>)
    ensures
        r == spec_rebind(*decl, *ps, name),
    decreases ps,
{
    match decl {
        List::Nil => None,
        List::Cons(d, drest) => match ps {
            List::Nil => None,
            List::Cons((p, t), prest) => if *d == name {
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
        Ok(dt) => if !integer(t) {
            Err(Refusal::Convert(line))
        } else if op == BinOp::Div {
            Ok(DExpr::DivIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
        } else {
            Ok(DExpr::RemIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db))), dt))
        },
    }
}

pub fn integer(t: Ty) -> (r: bool)
    ensures
        r == is_integer(t),
{
    t == Ty::I32 || t == Ty::I64 || t == Ty::U8 || t == Ty::U32 || t == Ty::U64 || t == Ty::I8 || t == Ty::I16 || t == Ty::U16
}

pub fn width(t: Ty) -> (r: u32)
    ensures
        r == spec_width(t),
{
    match t {
        Ty::I8 => 8,
        Ty::U8 => 8,
        Ty::I16 => 16,
        Ty::U16 => 16,
        Ty::I32 => 32,
        Ty::U32 => 32,
        _ => 64,
    }
}

pub fn shift(da: DExpr, dn: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_shift(da, dn, t, line),
{
    match translate_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !integer(t) {
            Err(Refusal::Convert(line))
        } else {
            Ok(DExpr::ShrIn(Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(dn))), dt, width(t)))
        },
    }
}

pub fn translate_leaf(d: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_leaf(d, t, line),
{
    match translate_ty(t, line) {
        Ok(_) => if integer(t) {
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
        Expr::Enumerator(k, i) => Ok(DExpr::Enumerator(*k, *i)),
        Expr::Bool(b) => Ok(DExpr::Bool(*b)),
        Expr::Name(n) => if has(bound, *n) {
            Ok(DExpr::Bound(*n))
        } else {
            match rebind(decl, ps, *n) {
                Some((p, t)) => translate_leaf(contract_var(p, t), view_ty(t), line),
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
        Expr::Bin(op, a, b) if (*op == BinOp::Eq || *op == BinOp::Ne) && (a.is_nullopt() || b.is_nullopt()) => if b.is_nullopt() {
            match path(a, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Ptr(_))) => Ok(null_test(*op, d)),
                Ok((d, Ty::Own(_))) => Ok(null_test(*op, d)),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            }
        } else {
            match path(b, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Ptr(_))) => Ok(null_test(*op, d)),
                Ok((d, Ty::Own(_))) => Ok(null_test(*op, d)),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            }
        },
        Expr::Bin(_, a, b) if ptr_operand(a, decl, ps, ret, bound, line, sd) || ptr_operand(b, decl, ps, ret, bound, line, sd) => Err(Refusal::Syntax(line)),
        Expr::Bin(op, a, b) => if ordered(*op) && (enum_operand(a, decl, ps, ret, bound, line, sd) || enum_operand(b, decl, ps, ret, bound, line, sd)) {
            Err(Refusal::Syntax(line))
        } else {
            match translate_contract(a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(binary(*op, da, db)),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
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
            let inner = List::Cons(*j, Box::new(copy(bound)));
            match translate_contract(body, decl, ps, ret, &inner, line, sd) {
                Ok(db) => Ok(DExpr::Forall(*j, Box::new(db))),
                Err(r) => Err(r),
            }
        },
        Expr::Exists(j, body) => {
            let inner = List::Cons(*j, Box::new(copy(bound)));
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
            Ok((d, Ty::Ptr(s))) => translate_leaf(DExpr::Get(Box::new(d)), elem(s), line),
            Ok((d, Ty::Own(s))) => translate_leaf(DExpr::Get(Box::new(d)), elem(s), line),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::Apply(f, args) => if has(bound, *f) {
            Err(Refusal::Syntax(line))
        } else {
            match functor(*f, decl, ps, ret, bound, sd) {
            Some((d, k)) => match member(sd, k, CALL_OP) {
                Some((key, Some((rt, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match object(ps, ret) {
            Some((o, k)) => match member(sd, k, *f) {
                Some((key, Some((t, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(o, Box::new(convert(da, &tail(&mps)))))), t, line),
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
                        Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    _ => Err(Refusal::NotPure(*f, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
            Err(r) => Err(r),
        },
        Expr::Chain(_, _, a, b, c) if ptr_operand(a, decl, ps, ret, bound, line, sd) || ptr_operand(b, decl, ps, ret, bound, line, sd)
            || ptr_operand(c, decl, ps, ret, bound, line, sd) => Err(Refusal::Syntax(line)),
        Expr::Chain(o1, o2, a, b, c) => if chain_ok(*o1, *o2) && !(enum_operand(a, decl, ps, ret, bound, line, sd) || enum_operand(b, decl, ps, ret, bound, line, sd)
            || enum_operand(c, decl, ps, ret, bound, line, sd)) {
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
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => match translate_contract_args(rest, decl, ps, ret, bound, line, sd) {
                Ok(dr) => Ok(List::Cons(da, Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn field_ty(sd: &Structs, k: u32, f: u32) -> (r: Option<Ty>)
    ensures
        r == spec_field_ty(*sd, k, f),
{
    match fields_of(sd, k) {
        Some(fields) => get(fields, f),
        None => None,
    }
}

pub fn ordered(op: BinOp) -> (r: bool)
    ensures
        r == spec_ordered(op),
{
    op == BinOp::Lt || op == BinOp::Le || op == BinOp::Gt || op == BinOp::Ge
}

pub fn enum_operand(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_enum_operand(*e, *decl, *ps, ret, *bound, line, *sd),
    decreases e, 1nat,
{
    match e {
        Expr::Enumerator(_, _) => true,
        Expr::Paren(a) => enum_operand(a, decl, ps, ret, bound, line, sd),
        Expr::Old(a) => enum_operand(a, decl, &before(ps), ret, bound, line, sd),
        Expr::Cond(_, a, b) => enum_operand(a, decl, ps, ret, bound, line, sd) || enum_operand(b, decl, ps, ret, bound, line, sd),
        Expr::Result => match ret {
            Some(Ty::Enum(_)) => true,
            _ => false,
        },
        _ => match path(e, decl, ps, ret, bound, line, sd) {
            Ok((_, Ty::Enum(_))) => true,
            _ => false,
        },
    }
}

pub fn ptr_operand(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_ptr_operand(*e, *decl, *ps, ret, *bound, line, *sd),
    decreases e, 1nat,
{
    match e {
        Expr::Paren(a) => ptr_operand(a, decl, ps, ret, bound, line, sd),
        Expr::Old(a) => ptr_operand(a, decl, &before(ps), ret, bound, line, sd),
        Expr::Cond(_, a, b) => ptr_operand(a, decl, ps, ret, bound, line, sd) || ptr_operand(b, decl, ps, ret, bound, line, sd),
        _ => match path(e, decl, ps, ret, bound, line, sd) {
            Ok((_, Ty::Ptr(_))) => true,
            Ok((_, Ty::Own(_))) => true,
            _ => false,
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
                Some((p, t)) => Ok((contract_var(p, t), view_ty(t))),
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
        Expr::Value(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Opt(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok((d, Ty::Ptr(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok((d, Ty::Own(Scalar::Struct(k)))) => Ok((DExpr::Get(Box::new(d)), Ty::Struct(k))),
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
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
        List::Nil => None,
        List::Cons((p, t), rest) => match t {
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
        List::Cons((p, t), rest) => match t {
            Ty::This(_) => Some((*p, *t)),
            Ty::ThisMut(_) => Some((*p, *t)),
            Ty::ThisAfter(_) => Some((*p, *t)),
            _ => self_param(rest),
        },
        List::Nil => None,
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
        List::Nil => List::Nil,
        List::Cons((p, t), rest) => {
            let v = match t {
                Ty::ThisMut(k) => Ty::ThisAfter(*k),
                Ty::Mut(s) => Ty::MutAfter(*s),
                Ty::MutSeq(s) => Ty::MutSeqAfter(*s),
                _ => *t,
            };
            List::Cons((*p, v), Box::new(after(rest)))
        },
    }
}

pub fn before(ps: &Params) -> (r: Params)
    ensures
        r == spec_before(*ps),
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((p, t), rest) => {
            let v = match t {
                Ty::ThisAfter(k) => Ty::ThisMut(*k),
                Ty::MutAfter(s) => Ty::Mut(*s),
                Ty::MutSeqAfter(s) => Ty::MutSeq(*s),
                _ => *t,
            };
            List::Cons((*p, v), Box::new(before(rest)))
        },
    }
}

pub fn has_after(ps: &Params) -> (r: bool)
    ensures
        r == spec_has_after(*ps),
{
    match self_param(ps) {
        Some((_, Ty::ThisAfter(_))) => true,
        _ => any_after(ps),
    }
}

pub fn any_after(ps: &Params) -> (r: bool)
    ensures
        r == spec_any_after(*ps),
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => match t {
            Ty::MutAfter(_) => true,
            Ty::MutSeqAfter(_) => true,
            _ => any_after(rest),
        },
    }
}

pub fn is_mut(ps: &Params, name: u32) -> (r: bool)
    ensures
        r == spec_is_mut(*ps, name),
{
    match get(ps, name) {
        Some(Ty::Mut(_)) => true,
        _ => false,
    }
}

pub fn written(t: Ty) -> (r: bool)
    ensures
        r == spec_written(t),
{
    match t {
        Ty::ThisMut(_) => true,
        Ty::Mut(_) => true,
        Ty::MutSeq(_) => true,
        _ => false,
    }
}

pub fn mutates(ps: &Params) -> (r: bool)
    ensures
        r == spec_mutates(*ps),
    decreases ps,
{
    match ps {
        List::Nil => false,
        List::Cons((_, t), rest) => written(*t) || mutates(rest),
    }
}

pub fn outs(ps: &Params) -> (r: DParams)
    ensures
        r == spec_outs(*ps),
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Mut(s) => List::Cons((*n, scalar_dty(*s)), Box::new(outs(rest))),
            Ty::MutSeq(s) => List::Cons((*n, DTy::Seq(*s)), Box::new(outs(rest))),
            _ => outs(rest),
        },
    }
}

pub fn modifies(ps: &Params, cs: &Conds, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_modifies(*ps, *cs, line),
{
    match bad_modifies(ps, cs) {
        Some(r) => Some(r),
        None => unlisted(ps, ps, cs, line),
    }
}

pub fn bad_modifies(ps: &Params, cs: &Conds) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_modifies(*ps, *cs),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, decl), rest) => if *k == CondKind::Modifies {
            match e {
                Expr::Name(n) => match rebind(decl, ps, *n) {
                    Some((_, Ty::Mut(_))) => bad_modifies(ps, rest),
                    Some((_, Ty::MutSeq(_))) => bad_modifies(ps, rest),
                    _ => Some(Refusal::NotRef(*n, *l)),
                },
                _ => Some(Refusal::Syntax(*l)),
            }
        } else {
            bad_modifies(ps, rest)
        },
    }
}

pub fn lists(ps: &Params, cs: &Conds, p: u32) -> (r: bool)
    ensures
        r == spec_lists(*ps, *cs, p),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => {
            let here = *k == CondKind::Modifies && match e {
                Expr::Name(n) => match rebind(decl, ps, *n) {
                    Some((q, _)) => q == p,
                    None => false,
                },
                _ => false,
            };
            here || lists(ps, rest, p)
        },
    }
}

pub fn unlisted(todo: &Params, ps: &Params, cs: &Conds, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_unlisted(*todo, *ps, *cs, line),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => match t {
            Ty::Mut(_) | Ty::MutSeq(_) => if lists(ps, cs, *p) {
                unlisted(rest, ps, cs, line)
            } else {
                Some(Refusal::Unlisted(*p, line))
            },
            _ => unlisted(rest, ps, cs, line),
        },
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
        copy(ps)
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

pub fn param_ty(t: Ty, line: u32, sd: &Structs) -> (r: Result<DTy, Refusal>)
    ensures
        r == spec_param_ty(t, line, *sd),
{
    match t {
        Ty::ThisAfter(_) => Err(Refusal::Syntax(line)),
        Ty::MutAfter(_) => Err(Refusal::Syntax(line)),
        Ty::MutSeqAfter(_) => Err(Refusal::Syntax(line)),
        Ty::Opt(Scalar::Struct(k)) => if holds_seq(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            translate_ty(t, line)
        },
        Ty::Ptr(Scalar::Struct(k)) => if holds_seq(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            translate_ty(t, line)
        },
        Ty::Own(Scalar::Struct(k)) => if holds_seq(sd, k) {
            Err(Refusal::HoldsSeq(line))
        } else {
            translate_ty(t, line)
        },
        _ => translate_ty(t, line),
    }
}

pub fn translate_params(ps: &Params, line: u32, sd: &Structs) -> (r: Result<DParams, Refusal>)
    ensures
        r == spec_params(*ps, line, *sd),
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        List::Cons((n, t), rest) => match param_ty(*t, line, sd) {
            Ok(dt) => match translate_params(rest, line, sd) {
                Ok(dr) => Ok(List::Cons((*n, dt), Box::new(dr))),
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
    translate_params(&f.params, f.line, sd).is_ok() && ret_ty(f.ret, f.line, sd).is_ok() && modifies(&f.params, &f.conds, f.line).is_none()
}

pub fn callable(fs: &Fns, key: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_callable(*fs, key, *sd),
    decreases fs,
{
    match fs {
        List::Nil => false,
        List::Cons(f, rest) => (f.name == key && signature(f, sd)) || callable(rest, key, sd),
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
        Stmt::RangeFor(_, _, _, _, _, _, l) => *l,
        Stmt::SetField(_, _, l) => *l,
        Stmt::SetRefField(_, _, _, l) => *l,
        Stmt::Switch(_, _, _, l) => *l,
        Stmt::Call(_, _, _, l) => *l,
        Stmt::Exit(l) => *l,
        Stmt::Assert(_, l) => *l,
        Stmt::Apply(_, _, l) => *l,
        Stmt::SetIndex(_, _, _, l) => *l,
        Stmt::PushBack(_, _, l) => *l,
        Stmt::Unknown(_, l) => *l,
    }
}

pub fn scope(s: &Stmt, env: &Params) -> (r: Params)
    ensures
        r == spec_scope(*s, *env),
{
    match s {
        Stmt::Local(n, t, _, _) => List::Cons((*n, *t), Box::new(copy(env))),
        _ => copy(env),
    }
}


pub fn index_of(cs: &Conds, fresh: u32) -> (r: Result<(u32, u32), Refusal>)
    ensures
        r == spec_index_of(*cs, fresh),
    decreases cs,
{
    match cs {
        List::Nil => Ok((fresh, 0)),
        List::Cons((k, e, l, _), rest) => match index_of(rest, fresh) {
            Err(r) => Err(r),
            Ok((n, l2)) => if *k == CondKind::Index {
                if l2 != 0 {
                    Err(Refusal::Syntax(l2))
                } else {
                    match e {
                        Expr::Name(m) => Ok((*m, *l)),
                        _ => Err(Refusal::Syntax(*l)),
                    }
                }
            } else {
                Ok((n, l2))
            },
        },
    }
}

pub fn range_bound(i: u32, v: u32) -> (r: Expr)
    ensures
        r == spec_range_bound(i, v),
{
    Expr::Bin(BinOp::Le, Box::new(Expr::Name(i)), Box::new(Expr::Size(Box::new(Expr::Name(v)))))
}

pub fn range_measure(i: u32, v: u32) -> (r: Expr)
    ensures
        r == spec_range_measure(i, v),
{
    Expr::Bin(BinOp::Sub, Box::new(Expr::Size(Box::new(Expr::Name(v)))), Box::new(Expr::Name(i)))
}

pub fn range_test(i: u32, v: u32, s: Scalar, ext: Extent) -> (r: Expr)
    ensures
        r == spec_range_test(i, v, s, ext),
{
    Expr::Bin(BinOp::Lt, Box::new(Expr::Var(i, Ty::U64)), Box::new(Expr::Size(Box::new(Expr::Var(v, Ty::Seq(s, ext))))))
}

pub fn range_elem(i: u32, v: u32, s: Scalar, ext: Extent) -> (r: Expr)
    ensures
        r == spec_range_elem(i, v, s, ext),
{
    Expr::Index(Box::new(Expr::Var(v, Ty::Seq(s, ext))), Box::new(Expr::Var(i, Ty::U64)))
}

pub fn range_zero() -> (r: DExpr)
    ensures
        r == spec_range_zero(),
{
    DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(0)))
}

pub fn translate_loop_conds(cs: &Conds, want: CondKind, env: &Params, sd: &Structs, ranged: bool) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_loop_conds(*cs, want, *env, *sd, ranged),
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((k, e, l, _), rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Requires => Err(Refusal::Misplaced(*l)),
            CondKind::Ensures => Err(Refusal::Misplaced(*l)),
            CondKind::Modifies => Err(Refusal::Misplaced(*l)),
            CondKind::Index if !ranged => Err(Refusal::Misplaced(*l)),
            _ => match translate_loop_conds(rest, want, env, sd, ranged) {
                Ok(dr) => if *k == want {
                    match translate_contract(e, &keys(env), &after(env), None, &List::Nil, *l, sd) {
                        Ok(d) => Ok(List::Cons((d, *l), Box::new(dr))),
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
        Some(f) => mutates(&f.params),
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
            Ty::Mut(_) => if is_mut(ps, *v) {
                Ok(Obj::Out(*v))
            } else {
                Err(Refusal::Syntax(line))
            },
            Ty::MutSeq(_) => Err(Refusal::PassOn(*v, line)),
            _ => if get(ps, *v).is_some() {
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

pub fn writebacks(args: &Args, cps: &Params, ps: &Params, line: u32) -> (r: Result<Objs, Refusal>)
    ensures
        r == spec_writebacks(*args, *cps, *ps, line),
    decreases args,
{
    match args {
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match cps {
            List::Nil => Err(Refusal::Syntax(line)),
            List::Cons((_, t), crest) => if written(*t) {
                match target(a, ps, line) {
                    Err(r) => Err(r),
                    Ok(o) => match writebacks(rest, crest, ps, line) {
                        Err(r) => Err(r),
                        Ok(os) => Ok(List::Cons(o, Box::new(os))),
                    },
                }
            } else {
                writebacks(rest, crest, ps, line)
            },
        },
    }
}

pub fn callee_writebacks(all: &Fns, key: u32, args: &Args, ps: &Params, line: u32) -> (r: Result<Objs, Refusal>)
    ensures
        r == spec_callee_writebacks(*all, key, *args, *ps, line),
{
    match find(all, key) {
        Some(f) => writebacks(args, &f.params, ps, line),
        None => Err(Refusal::Syntax(line)),
    }
}

pub fn call_stmt(key: u32, name: u32, args: &Args, line: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_call_stmt(key, name, *args, line, *all, *ps, *sd),
{
    if callee_writes(all, key) {
        match callee_writebacks(all, key, args, ps, line) {
            Err(r) => Err(r),
            Ok(os) => match call_lift(key, name, args, line, all, line, sd) {
                Ok((c, da)) => Ok(pre(c, DStmt::Update(os, key, da))),
                Err(r) => Err(r),
            },
        }
    } else {
        match call_lift(key, name, args, line, all, line, sd) {
            Ok((c, da)) => if callee_void(all, key) {
                Ok(pre(c, DStmt::CallStmt(key, da)))
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
        match callee_writebacks(all, key, args, ps, line) {
            Err(r) => Err(r),
            Ok(os) => match call_lift(key, name, args, at, all, line, sd) {
                Ok((c, da)) => Ok(pre(c, DStmt::LocalUpdate(n, dt, os, key, da))),
                Err(r) => Err(r),
            },
        }
    } else {
        match call_lift(key, name, args, at, all, line, sd) {
            Ok((c, da)) => Ok(pre(c, DStmt::LocalCall(n, dt, key, da))),
            Err(r) => Err(r),
        }
    }
}

pub fn step(n: u32, dt: DTy, up: bool, out: bool) -> (r: DStmt)
    ensures
        r == spec_step(n, dt, up, out),
{
    let op = if up {
        BinOp::Add
    } else {
        BinOp::Sub
    };
    let one = Box::new(DExpr::Conv(dt, Box::new(DExpr::Lit(1))));
    if out {
        DStmt::SetOut(n, DExpr::Bin(op, Box::new(DExpr::Out(n)), one))
    } else {
        DStmt::Assign(n, DExpr::Bin(op, Box::new(DExpr::Var(n)), one))
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
                match call_lift(*k, *n, args, *at, all, *l, sd) {
                    Ok((c, da)) => Ok(pre(c, DStmt::ReturnCall(*k, da))),
                    Err(r) => Err(r),
                }
            },
            _ => match lift(e, all, *l, sd, 0, true) {
                Ok((c, d, _)) => Ok(pre(c, DStmt::Return(d))),
                Err(r) => Err(r),
            },
        },
        Stmt::If(c, t, f, l) => match lift(c, all, *l, sd, 0, true) {
            Ok((cc, dc, _)) => match translate_stmts(t, all, env, ps, sd) {
                Ok(dt) => match translate_stmts(f, all, env, ps, sd) {
                    Ok(df) => Ok(pre(cc, DStmt::If(dc, Box::new(dt), Box::new(df)))),
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
                _ => match lift(e, all, *l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(pre(c, DStmt::Local(*n, dt, d))),
                    Err(r) => Err(r),
                },
            },
        },
        Stmt::Assign(n, e, l) => if is_mut(ps, *n) {
            match lift(e, all, *l, sd, 0, true) {
                Ok((c, d, _)) => Ok(pre(c, DStmt::SetOut(*n, d))),
                Err(r) => Err(r),
            }
        } else if get(ps, *n).is_some() {
            Err(Refusal::WriteParam(*n, *l))
        } else {
            match e {
                Expr::Call(k, nm, args, at) => if callee_writes(all, *k) {
                    Err(Refusal::Place(*at))
                } else {
                    match call_lift(*k, *nm, args, *at, all, *l, sd) {
                        Ok((c, da)) => Ok(pre(c, DStmt::AssignCall(*n, *k, da))),
                        Err(r) => Err(r),
                    }
                },
                _ => match lift(e, all, *l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(pre(c, DStmt::Assign(*n, d))),
                    Err(r) => Err(r),
                },
            }
        },
        Stmt::Step(n, t, up, l) => if get(ps, *n).is_some() && !is_mut(ps, *n) {
            Err(Refusal::WriteParam(*n, *l))
        } else {
            match translate_ty(*t, *l) {
                Err(r) => Err(r),
                Ok(dt) => Ok(step(*n, dt, *up, is_mut(ps, *n))),
            }
        },
        Stmt::While(c, lc, body, l) => match translate_loop_conds(lc, CondKind::Invariant, env, sd, false) {
            Err(r) => Err(r),
            Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, env, sd, false) {
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
            match translate_loop_conds(lc, CondKind::Invariant, &inner, sd, false) {
                Err(r) => Err(r),
                Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, &inner, sd, false) {
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
        Stmt::RangeFor(fresh, x, xt, seq, lc, body, l) => match index_of(lc, *fresh) {
            Err(r) => Err(r),
            Ok((i, il)) => if has(&keys(env), i) || this_field(ps, None, i, sd).is_some() {
                Err(Refusal::IndexName(i, il))
            } else {
                match seq {
                    Expr::Var(v, Ty::Seq(s, ext)) => if *xt != elem(*s) {
                        Err(Refusal::Syntax(*l))
                    } else {
                        let inner: Params = List::Cons((i, Ty::U64), Box::new(copy(env)));
                        match translate_loop_conds(lc, CondKind::Invariant, &inner, sd, true) {
                            Err(r) => Err(r),
                            Ok(inv) => match translate_loop_conds(lc, CondKind::Decreases, &inner, sd, true) {
                                Err(r) => Err(r),
                                Ok(dec) => match translate_contract(&range_bound(i, *v), &keys(&inner), &after(&inner), None, &List::Nil, *l, sd) {
                                    Err(r) => Err(r),
                                    Ok(dbound) => match translate_contract(&range_measure(i, *v), &keys(&inner), &after(&inner), None, &List::Nil, *l, sd) {
                                        Err(r) => Err(r),
                                        Ok(dmeasure) => match translate_code(&range_test(i, *v, *s, *ext), *l) {
                                            Err(r) => Err(r),
                                            Ok(dc) => match translate_value_ty(*xt, *l, sd) {
                                                Err(r) => Err(r),
                                                Ok(dt) => match translate_code(&range_elem(i, *v, *s, *ext), *l) {
                                                    Err(r) => Err(r),
                                                    Ok(de) => {
                                                        let turn: Params = List::Cons((*x, *xt), Box::new(copy(&inner)));
                                                        match translate_stmts(body, all, &turn, ps, sd) {
                                                            Err(r) => Err(r),
                                                            Ok(db) => {
                                                                let dec2 = match dec {
                                                                    List::Nil => List::Cons((dmeasure, *l), Box::new(List::Nil)),
                                                                    d => d,
                                                                };
                                                                Ok(
                                                                    DStmt::For(
                                                                        Box::new(DStmt::Local(i, DTy::UInt64, range_zero())),
                                                                        *l,
                                                                        dc,
                                                                        List::Cons((dbound, *l), Box::new(inv)),
                                                                        dec2,
                                                                        Box::new(List::Cons((Box::new(DStmt::Local(*x, dt, de)), *l), Box::new(db))),
                                                                        Box::new(step(i, DTy::UInt64, true, false)),
                                                                        *l,
                                                                    ),
                                                                )
                                                            },
                                                        }
                                                    },
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        }
                    },
                    _ => Err(Refusal::Syntax(*l)),
                }
            },
        },
        Stmt::SetField(f, e, l) => match self_param(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match field_ty(sd, k, *f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(*l)),
                    Some(_) => match lift(e, all, *l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(pre(c, DStmt::SetField(*f, d))),
                        Err(r) => Err(r),
                    },
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::WriteParam(p, *l)),
            },
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::SetRefField(p, f, e, l) => match get(ps, *p) {
            Some(Ty::Mut(Scalar::Struct(k))) => match field_ty(sd, k, *f) {
                Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(*l)),
                Some(_) => match lift(e, all, *l, sd, 0, true) {
                    Ok((c, d, _)) => Ok(pre(c, DStmt::SetOutField(*p, *f, d))),
                    Err(r) => Err(r),
                },
                None => Err(Refusal::NoField(*f, *l)),
            },
            Some(_) => Err(Refusal::WriteParam(*p, *l)),
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::Switch(e, k, cs, l) => match lift(e, all, *l, sd, 0, true) {
            Ok((c, d, _)) => match translate_cases(cs, all, env, ps, sd) {
                Ok(dc) => Ok(pre(c, DStmt::Match(d, *k, Box::new(dc)))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Call(k, nm, args, l) => call_stmt(*k, *nm, args, *l, all, ps, sd),
        Stmt::Exit(_) => Ok(DStmt::Exit),
        Stmt::Assert(e, l) => match translate_contract(e, &keys(env), &after(env), None, &List::Nil, *l, sd) {
            Ok(d) => Ok(DStmt::Assert(d)),
            Err(r) => Err(r),
        },
        Stmt::Apply(f, args, l) => match translate_contract_args(args, &keys(env), &after(env), None, &List::Nil, *l, sd) {
            Ok(da) => Ok(DStmt::Apply(*f, da)),
            Err(r) => Err(r),
        },
        Stmt::SetIndex(v, i, e, l) => match get(ps, *v) {
            Some(Ty::MutSeq(_)) => match translate_code(i, *l) {
                Ok(di) => match translate_code(e, *l) {
                    Ok(de) => Ok(DStmt::SetOut(*v, DExpr::SetAt(Box::new(DExpr::Out(*v)), Box::new(di), Box::new(de)))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(*v, *l)),
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::PushBack(v, e, l) => match get(ps, *v) {
            Some(Ty::MutSeq(_)) => match translate_code(e, *l) {
                Ok(de) => Ok(DStmt::SetOut(*v, DExpr::Append(Box::new(DExpr::Out(*v)), Box::new(de)))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(*v, *l)),
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_cases(cs: &Cases, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DCases, Refusal>)
    ensures
        r == spec_cases(*cs, *all, *env, *ps, *sd),
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((i, body), rest) => match translate_stmts(body, all, env, ps, sd) {
            Ok(db) => match translate_cases(rest, all, env, ps, sd) {
                Ok(dr) => Ok(List::Cons((*i, Box::new(db)), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub fn translate_stmts(ss: &Stmts, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts(*ss, *all, *env, *ps, *sd),
    decreases ss,
{
    match ss {
        List::Nil => Ok(List::Nil),
        List::Cons(s, rest) => match translate_stmt(s, all, env, ps, sd) {
            Ok(d) => match translate_stmts(rest, all, &scope(s, env), ps, sd) {
                Ok(dr) => Ok(List::Cons((Box::new(d), place(s)), Box::new(dr))),
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
        List::Nil => false,
        List::Cons(a, rest) => has_result(a) || has_result_args(rest),
    }
}

pub fn translate_conds(cs: &Conds, want: CondKind, ps: &Params, ret: Ty, sd: &Structs) -> (r: Result<DConds, Refusal>)
    ensures
        r == spec_conds(*cs, want, *ps, ret, *sd),
    decreases cs,
{
    match cs {
        List::Nil => Ok(List::Nil),
        List::Cons((k, e, l, decl), rest) => match k {
            CondKind::Other(w) => Err(Refusal::Construct(*w, *l)),
            CondKind::Bad(r) => Err(*r),
            CondKind::Invariant => Err(Refusal::Misplaced(*l)),
            CondKind::Index => Err(Refusal::Misplaced(*l)),
            _ => match translate_conds(rest, want, ps, ret, sd) {
                Ok(dr) => if *k == want && *k == CondKind::Decreases && has_result(e) {
                    Err(Refusal::Syntax(*l))
                } else if *k == want {
                    match translate_contract(e, decl, &view_ps(ps, *k), Some(view_ret(ret, *k)), &List::Nil, *l, sd) {
                        Ok(d) => Ok(List::Cons((d, *l), Box::new(dr))),
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
        List::Nil => None,
        List::Cons((n, _), rest) => if holds(seen, *n) {
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
        Stmt::Switch(_, _, cs, _) => twice_cases(seen, cs),
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
        Stmt::RangeFor(fresh, x, _, _, lc, body, l) => {
            match index_of(lc, *fresh) {
                Ok((i, _)) => if !holds(seen, i) {
                    seen.push(i);
                },
                Err(_) => {},
            }
            if holds(seen, *x) {
                Some((*x, *l))
            } else {
                seen.push(*x);
                twice_stmts(seen, body)
            }
        },
        _ => None,
    }
}

pub fn twice_cases(seen: &mut Vec<u32>, cs: &Cases) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice_cases(old(seen)@, *cs).0,
        final(seen)@ == spec_twice_cases(old(seen)@, *cs).1,
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => {
            let r = twice_stmts(seen, body);
            if r.is_some() {
                r
            } else {
                twice_cases(seen, rest)
            }
        },
    }
}

pub fn twice_stmts(seen: &mut Vec<u32>, ss: &Stmts) -> (r: Option<(u32, u32)>)
    ensures
        r == spec_twice_stmts(old(seen)@, *ss).0,
        final(seen)@ == spec_twice_stmts(old(seen)@, *ss).1,
    decreases ss,
{
    match ss {
        List::Nil => None,
        List::Cons(s, rest) => {
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
        List::Nil => None,
        List::Cons(s, rest) => match misreturn_stmt(s, void) {
            Some(l) => Some(l),
            None => misreturn(rest, void),
        },
    }
}

pub fn misreturn_cases(cs: &Cases, void: bool) -> (r: Option<u32>)
    ensures
        r == spec_misreturn_cases(*cs, void),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => match misreturn(body, void) {
            Some(l) => Some(l),
            None => misreturn_cases(rest, void),
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
        Stmt::Switch(_, _, cs, _) => misreturn_cases(cs, void),
        Stmt::For(init, _, step, _, body, _) => match misreturn_stmt(init, void) {
            Some(l) => Some(l),
            None => match misreturn_stmt(step, void) {
                Some(l) => Some(l),
                None => misreturn(body, void),
            },
        },
        Stmt::RangeFor(_, _, _, _, _, body, _) => misreturn(body, void),
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
                    Ok((req, ens, dec, List::Nil))
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
        List::Nil => tail,
        List::Cons((n, t), rest) => match t {
            Ty::Seq(_, Extent::Fixed(k)) => List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Var(*n)))), Box::new(DExpr::Lit(*k))), line), Box::new(bounds(rest, line, tail))),
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
        DExpr::Out(x0) => DExpr::Out(*x0),
        DExpr::Enumerator(k, i) => DExpr::Enumerator(*k, *i),
        DExpr::Ite(x0, x1, x2) => DExpr::Ite(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::Temp(x0) => DExpr::Temp(*x0),
        DExpr::ShrIn(x0, x1, x2, x3) => DExpr::ShrIn(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), *x2, *x3),
        DExpr::SetAt(x0, x1, x2) => DExpr::SetAt(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::Append(x0, x1) => DExpr::Append(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::CountIf(x0, x1, x2, x3) => DExpr::CountIf(Box::new(copy_dexpr(x0)), *x1, *x2, Box::new(copy_dexpr(x3))),
    }
}

pub fn copy_dargs(a: &DArgs) -> (r: DArgs)
    ensures
        r == *a,
    decreases a,
{
    match a {
        List::Nil => List::Nil,
        List::Cons(d, rest) => List::Cons(copy_dexpr(d), Box::new(copy_dargs(rest))),
    }
}

pub fn pure_body(ps: &Params, body: &DStmts) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_body(*ps, *body),
{
    match this_param(ps) {
        Some(_) => if mutates(ps) {
            None
        } else {
            match body {
                List::Cons((s, _), rest) => match &**rest {
                    List::Nil => match &**s {
                        DStmt::Return(d) => Some(copy_dexpr(d)),
                        _ => None,
                    },
                    _ => None,
                },
                List::Nil => None,
            }
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
        List::Nil => List::Nil,
        List::Cons((p, _), rest) => List::Cons(DExpr::Var(*p), Box::new(param_args(rest))),
    }
}

pub fn linked(f: &Function, ens: DConds, pure: &Option<DExpr>) -> (r: DConds)
    ensures
        r == spec_linked(*f, ens, *pure),
{
    match pure {
        Some(_) => append(
            ens,
            List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(param_args(&f.params))))), f.line), Box::new(List::Nil)),
        ),
        None => ens,
    }
}

pub fn member(sd: &Structs, k: u32, name: u32) -> (r: Option<(u32, Option<(Ty, Params)>)>)
    ensures
        r == spec_member(*sd, k, name),
{
    match get_ref(sd, k) {
        Some((_, _, ms)) => match get_ref(ms, name) {
            Some((key, Some((rt, mps)))) => Some((*key, Some((*rt, copy(mps))))),
            Some((key, None)) => Some((*key, None)),
            None => None,
        },
        None => None,
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
        List::Nil => None,
        List::Cons(f, rest) => if f.name == key {
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
                    Some(_) => Some((f.ret, copy(&f.params))),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match translate_stmts(&f.body, all, &f.params, &f.params, sd) {
                Ok(body) => match pure_body(&f.params, &body) {
                    Some(_) => Some((f.ret, copy(&f.params))),
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
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((*n, (*key, pure_ret(all, *key, sd, strict))), Box::new(mark_members(rest, all, sd, strict))),
    }
}

pub fn mark(t: &Structs, all: &Fns, sd: &Structs, strict: bool) -> (r: Structs)
    ensures
        r == spec_mark(*t, *all, *sd, strict),
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => List::Cons((*k, (*l, copy(fields), mark_members(ms, all, sd, strict))), Box::new(mark(rest, all, sd, strict))),
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
        Ty::I8 => Some(DTy::Int8),
        Ty::I16 => Some(DTy::Int16),
        Ty::U16 => Some(DTy::UInt16),
        _ => None,
    }
}

pub fn tail(ps: &Params) -> (r: Params)
    ensures
        r == spec_tail(*ps),
{
    match ps {
        List::Cons((_, _), rest) => copy(rest),
        List::Nil => List::Nil,
    }
}

pub fn convert(da: DArgs, ps: &Params) -> (r: DArgs)
    ensures
        r == spec_convert(da, *ps),
    decreases da,
{
    match da {
        List::Nil => List::Nil,
        List::Cons(d, rest) => match ps {
            List::Cons((_, t), prest) => List::Cons(
                match int_dty(*t) {
                    Some(dt) => DExpr::Conv(dt, Box::new(d)),
                    None => d,
                },
                Box::new(convert(*rest, prest))),
            List::Nil => List::Cons(d, Box::new(convert(*rest, &List::Nil))),
        },
    }
}

pub fn translate_function(f: &Function, all: &Fns, sd: &Structs) -> (r: Model)
    ensures
        r == spec_function(*f, *all, *sd),
{
    match translate_params(&f.params, f.line, sd) {
        Err(r) => Model::Refused(r),
        Ok(ps) => match ret_ty(f.ret, f.line, sd) {
            Err(r) => Model::Refused(r),
            Ok(ret) => match modifies(&f.params, &f.conds, f.line) {
                Some(r) => Model::Refused(r),
                None => match translate_inside(f, all, sd) {
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
                                outs: outs(&f.params),
                                trusted: f.trusted,
                            },
                        )
                    },
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
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(translate_function(f, all, sd), Box::new(translate_each(rest, all, sd))),
    }
}

fn translate_fields(ps: &Params, line: u32) -> (r: Result<DParams, Refusal>)
    ensures
        r == spec_fields(*ps, line),
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        List::Cons((n, t), rest) => match if let Ty::Opt(Scalar::Struct(_)) | Ty::Ptr(_) | Ty::Own(_) = t { Err(Refusal::Element(line)) } else { translate_ty(*t, line) } {
            Ok(dt) => match translate_fields(rest, line) {
                Ok(dr) => Ok(List::Cons((*n, dt), Box::new(dr))),
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
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, _)), rest) => {
            let m = match translate_fields(fields, *l) {
                Ok(df) => Ok((*k, df)),
                Err(r) => Err(r),
            };
            List::Cons(m, Box::new(translate_structs(rest)))
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
    Enumerator(u32, u32),
    Old,
    Question,
    Colon,
    Arrow,
    Nullptr,
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
                            let (c, r) = match parse_add(toks, q + 1, line) {
                                Ok(x) => x,
                                Err(e) => return Err(e),
                            };
                            let first = Expr::Chain(op, op2, Box::new(a), Box::new(b), Box::new(c));
                            assert(!unknown_expr(first));
                            // A third comparison: the rest of the chain starts again at `b`, so the chains of two overlap, decision
                            // 0131. The parser reads `b` and `c` again from the same tokens, so the copies are equal.
                            // ponytail: the cost grows by a factor of three for each chain of three or more inside another. Contract
                            // lines are short. A chain node of any length is the upgrade.
                            if r < toks.len() {
                                if let Tok::Op(op3) = toks[r] {
                                    if is_cmp(op3) {
                                        return match parse_cmp(toks, p + 1, line) {
                                            Ok((rest, s)) => Ok((Expr::Bin(BinOp::And, Box::new(first), Box::new(rest)), s)),
                                            Err(e) => Err(e),
                                        };
                                    }
                                }
                            }
                            return Ok((first, r));
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
    } else if pos < toks.len() && toks[pos] == Tok::Op(BinOp::Mul) {
        // `*o` is `o.value()`, decision 0131. The translator refuses it on anything but an optional.
        match parse_unary(toks, pos + 1, line) {
            Ok((a, p)) => Ok((Expr::Value(Box::new(a)), p)),
            Err(e) => Err(e),
        }
    } else {
        parse_postfix(toks, pos, line)
    }
}

/// A token that follows an atom: `.size()`, `.name` or `[`.
fn is_postfix(t: Tok) -> bool {
    match t {
        Tok::Size | Tok::Field(_) | Tok::HasValue | Tok::Value | Tok::Empty | Tok::LBracket | Tok::Arrow => true,
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
                assert(!unknown_args(List::Nil));
                a = Expr::MApply(Box::new(a), f, Box::new(List::Nil));
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
        } else if toks[p] == Tok::Arrow {
            // `o->f` is `o.value().f`, decision 0137. A name of a field follows.
            if toks.len() - p > 1 {
                if let Tok::Ident(f) = toks[p + 1] {
                    let v = Expr::Value(Box::new(a));
                    assert(!unknown_expr(v));
                    a = Expr::Field(Box::new(v), f);
                    p = p + 2;
                } else {
                    return Err(Refusal::Syntax(line));
                }
            } else {
                return Err(Refusal::Syntax(line));
            }
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
            assert(!unknown_args(List::Nil));
            Ok((List::Cons(Box::new(a), Box::new(List::Nil)), p + 1))
        } else if p < toks.len() && toks[p] == Tok::Comma {
            match parse_args(toks, p + 1, line) {
                Ok((rest, q)) => Ok((List::Cons(Box::new(a), Box::new(rest)), q)),
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
            assert(!unknown_args(List::Nil));
            Ok((Expr::Apply(n, Box::new(List::Nil)), pos + 3))
        } else if toks.len() - pos > 1 && toks[pos + 1] == Tok::LParen {
            match parse_args(toks, pos + 2, line) {
                Ok((args, p)) => Ok((Expr::Apply(n, Box::new(args)), p)),
                Err(e) => Err(e),
            }
        } else {
            Ok((Expr::Name(n), pos + 1))
        },
        Tok::Result => Ok((Expr::Result, pos + 1)),
        Tok::Enumerator(k, i) => Ok((Expr::Enumerator(k, i), pos + 1)),
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
        Tok::Nullptr => Ok((Expr::Nullopt, pos + 1)),
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

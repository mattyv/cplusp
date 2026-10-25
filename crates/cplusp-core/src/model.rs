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
/// `Own` is a unique_ptr of a struct or an interface, as an element of a sequence only, decision 0170.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Scalar {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Struct(u32),
    Own(u32),
}

/// The extent of a sequence: no fixed length, or a fixed length, decision 0070.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Extent {
    Dynamic,
    Fixed(u64),
}

/// A type of the subset. `I8`, `I16` and `U16` are `int8_t`, `int16_t` and `uint16_t`, decision 0106. `F64` is `double`, a real
/// that is finite, decision 0150. `Seq` is a read-only sequence of a scalar with its extent, a parameter only, decisions 0064 and 0070.
/// `Struct` is a struct of the file by its key, decision 0073. `Opt` is a `std::optional` of a scalar, decision 0075. `This` is the
/// object of a `const` member function of the struct by its key, a parameter by value, decision 0089. `ThisMut` is the object of a
/// member function that writes it, which takes it in and gives it back, decision 0096. `ThisAfter` is that object after the call,
/// as an ensures line reads it, and `Fresh` is the result of a constructor before it exists, as its requires line reads it. The
/// translator makes these two views itself. `Mut` is a reference parameter that the function writes, which takes a value in and
/// gives it back, and `MutAfter` is its value after the call, as an ensures line reads it, decision 0108. `MutSeq` is a vector by
/// reference that the function writes, as a sequence, and `MutSeqAfter` is its value after the call, decision 0145. `Vec` is a local
/// `std::vector` that the function owns, a copy, decision 0160. `Enum` is an enum class of
/// the file by its key, decision 0109. `Iface` is `this` of a virtual function of the interface `k`, and `IfaceRef` is a parameter
/// `const B&` of it, through which a call runs an override, decision 0165. `IfaceMut` is `this` of a virtual function that writes
/// its object, decision 0169. `Void` is the result type
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
    F64,
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
    Vec(Scalar),
    Ptr(Scalar),
    Own(Scalar),
    Enum(u32),
    Fresh(u32),
    Iface(u32),
    IfaceRef(u32),
    IfaceMut(u32),
    Void,
    Other(u32),
}

/// A binary operator. In code it is the machine operator of its operand type. In a contract it is the operator on the exact
/// integers. `BitAnd` and `BitOr` are `&` and `|` on unsigned integers, the functions of the prelude, decision 0175.
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
    BitAnd,
    BitOr,
}

/// A cast that the compiler made or the author wrote. `Read` is the read of a variable, an lvalue-to-rvalue cast, and `NoOp` changes
/// nothing. Both keep the value. `Integral` is a cast from one integral type to another, by both types. `Construct` is the cast the
/// compiler writes around a construction, which keeps the value of the construction, decision 0070. `Upcast` is a value of a final
/// class to its interface, by their keys, decision 0166. `Other` is a cast with no rule yet, by the id of its kind.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CastKind {
    Read,
    NoOp,
    Integral(Ty, Ty),
    Construct,
    Upcast(u32, u32),
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
/// decision 0149. `RealLit` is a literal of type `double`, or a decimal with a point in a contract, by its digits and the count of
/// the digits after the point, decision 0150. `Ratio` is a literal of type `double` that is `m / q`, with `q` a power of two, and
/// no such decimal, decision 0158. `Finite` is `std::isfinite(e)` in a contract. `Abs` is `|e|`, and `Eps`, `Eta` and
/// `DblMax` are the words `eps`, `eta` and `DBL_MAX` of a contract, decision 0154. `Move` is `std::move(x)` of a local or a
/// parameter `x` of type `std::unique_ptr`, where C++ makes a new `std::unique_ptr` from it, by the name and the type of `x`,
/// decision 0171. `Bits` is `a & b` or `a | b` in code, with the type of its result, `StaticCast` is `static_cast<T>(e)` in a
/// contract, and `List` is a braced list `{a, b, c}` in code, decision 0175. `Step` is `x++`, `x--`, `++x` or `--x` inside an
/// expression, by the name and type of `x`, whether it adds one, and whether it is a prefix, decision 0177. `Fill` is the start
/// value `v(n, x)` of a local vector, by the count and the value, decision 0185. `Unknown` is a construct with no rule, by the id of
/// its kind and its line.
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
    RealLit(u64, u32),
    Ratio(u64, u64),
    Finite(Box<Expr>),
    Abs(Box<Expr>),
    Eps,
    Eta,
    DblMax,
    EmptyVec,
    Fill(Box<Expr>, Box<Expr>),
    Move(u32, Ty),
    Bits(BinOp, Box<Expr>, Box<Expr>, Ty),
    Step(u32, Ty, bool, bool),
    StaticCast(Ty, Box<Expr>),
    List(Box<Args>),
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
/// 0143. `SetIndex` is `v[i] = e` of a vector by reference, decision 0145, of a local vector, decision 0160, or of a local
/// std::array, decision 0184. `PushBack` is `v.push_back(e)`, decision 0148.
/// `Sort` is `std::sort(v.begin(), v.end())`, decision 0161, and `SortBy` is the same with a comparator lambda, by the names and the
/// type of its two parameters and the expression of its one `return`, decision 0162. `Block` is a bare block `{ ... }`, a scope of
/// its own, decision 0178. `SetOwnField` is `n->f = e` of a local `std::unique_ptr` of a plain struct, decision 0186. `SetFieldAt` is
/// `f[i] = e` of a sequence field in a member function that writes its object, decision 0187.
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
    SetOwnField(u32, u32, Expr, u32),
    Switch(Expr, u32, Box<Cases>, u32),
    Call(u32, u32, Box<Args>, u32),
    Exit(u32),
    Assert(Expr, u32),
    Apply(u32, Box<Args>, u32),
    RangeFor(u32, u32, Ty, Expr, Box<Conds>, Box<Stmts>, u32),
    SetIndex(u32, Expr, Expr, u32),
    SetFieldAt(u32, Expr, Expr, u32),
    PushBack(u32, Expr, u32),
    Sort(u32, u32),
    SortBy(u32, u32, u32, Ty, Expr, u32),
    Block(Box<Stmts>, u32),
    Unknown(u32, u32),
}

pub type Stmts = List<Box<Stmt>>;

/// The cases of a switch, each by the place of its enumerator among the enumerators, with its body, decision 0109. The plugin drops a
/// `break` that ends a case.
pub type Cases = List<(u32, Box<Stmts>)>;

/// The names and types of the parameters of a function, or of the fields of a struct, in their order.
pub type Params = List<(u32, Ty)>;

/// What a contract line says. `Modifies` names one reference parameter that the function writes, decision 0108. `Reads` names one
/// global that the function reads, decision 0173. `Other` is a word
/// the translator has no rule for yet, by the id of the word. `Bad` is a line that the shell could not cut or parse, with the refusal
/// it got.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CondKind {
    Requires,
    Ensures,
    Invariant,
    Decreases,
    Modifies,
    Reads,
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
    Real,
    Bool,
    Seq(Scalar),
    Struct(u32),
    Opt(Scalar),
    Enum(u32),
    Iface(u32),
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
/// of the width `W`, decision 0106. `SetAt` is `s[i := e]`, which Dafny proves is in range, decision 0145. `Append` is `s + [e]`, decision 0148. `CountIf` is `CountIf(s, (x: T) => e)` of the prelude, decision 0149. `RealLit` is the real `d / 10^k`, decision 0150. `FOp` is
/// one operation of the double model, `fadd` to `fdiv`, and `Abs`, `Eps`, `Eta` and `DblMax` are `abs`, `EPS`, `ETA` and `MAX` of it,
/// decision 0154. `FromInt` is `fint(e as int)` of it, the conversion of an integer, and `IntAbs` is `trunc_size(e)` of the prelude,
/// the absolute value of an integer, decision 0159. `Upcast` is `f_D'B(e)`, the value of a final class as its interface, decision
/// 0166. `Lemma` is `L(a); e`, the value `e` after a call of the lemma `L`, decision 0167. `Let` is `var x: T := e; b`, a local of
/// a pure body, decision 0172. `BitOp` is `BitAnd(a, b)` or `BitOr(a, b)` of the prelude on two naturals, and `SeqLit` is the
/// sequence `[a, b, c]`, decision 0175. `SeqFill` is `seq(n as int, _ => x)`, a sequence of `n` copies of `x`, decision 0185. A
/// Dafny expression calls no method.
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
    RealLit(u64, u32),
    FOp(BinOp, Box<DExpr>, Box<DExpr>),
    FromInt(Box<DExpr>),
    IntAbs(Box<DExpr>),
    Upcast(u32, u32, Box<DExpr>),
    Lemma(u32, Box<DArgs>, Box<DExpr>),
    Let(u32, DTy, Box<DExpr>, Box<DExpr>),
    BitOp(BinOp, Box<DExpr>, Box<DExpr>),
    SeqLit(Box<DArgs>),
    SeqFill(Box<DExpr>, Box<DExpr>),
    EmptySeq,
    Abs(Box<DExpr>),
    Eps,
    Eta,
    DblMax,
}

/// One step that runs before a statement, and sets a temporary of the statement by its number, of a type. `Call` sets it to the
/// value of a method by its key with its arguments, decision 0104. `Update` calls a method that writes back, and also writes the
/// places, decision 0177. `Step` writes `x += 1` or `x -= 1` of a name, `out` when it is a reference parameter, and sets the
/// temporary to the value before the write, or after it for a prefix, decision 0177.
#[derive(PartialEq, Eq, Debug)]
pub enum DPre {
    Call(u32, DTy, u32, DArgs),
    Update(u32, DTy, Objs, u32, DArgs),
    Step(u32, DTy, u32, bool, bool, bool),
}

/// The steps that run before a statement, in the order that they run, decisions 0104 and 0177.
pub type DCalls = List<DPre>;

pub type DArgs = List<DExpr>;

/// A Dafny statement. `Local` is `var x: T := e;`. `LocalCall` is `var x: T := m(args);`. `ReturnCall` is `result := m(args);
/// return;`, since Dafny takes no call in a `return`. `Assign` is `x := e;` and `AssignCall` is `x := m(args);`. `While` is the
/// condition, the invariants, the decreases lines and the body. `ReturnUpdate` is `result, o, x := m(o, x, args); return;` of a method that
/// writes back, decision 0174. `Moved` is a statement, then `x := None;` for each name that it
/// moves, decision 0171. `Gone` is a statement, then `x :| true;` of the vector `x` that it moves, or `x' :| true;` of a vector
/// reference parameter, decision 0185. `Block` is the statements of one `return` that runs a call only where C++ runs it, `DeclTemp` is
/// `var t: T;` of a temporary and `AssignTemp` is `t := e;`, decision 0177. `Scope` is a bare block `{ ... }`, `Dtors` is the calls
/// of the destructors of the locals that die at the end of a block, which is no statement of C++, and `SetResult` is
/// `result := e;` before the destructors run at a return, decision 0178. `For` prints as its start, then a `while` whose body ends with the
/// step. The start and the step keep their own places, decision 0069. `SetField` is `this' := this'.(f := e);`. `SetOut` is
/// `x' := e;` and `SetOutField` is `x' := x'.(f := e);` of a reference parameter, decision 0108. `Update` calls a method that writes
/// back, `o, x := m(o, x, args);`, and `LocalUpdate` also sets a new local to the value it gives, decisions 0096 and 0108. The
/// arguments hold each argument of the call. `CallStmt` is `m(args);` of a method that gives no value, and `Exit` is `return;`, decision 0096. `Assert` is
/// `assert e;` and `Apply` is `l(args);` of a lemma, decision 0099. `Sort` is `p := StdSort(p, (a: T, b: T) => a < b);` of a place
/// and the type of its elements, decision 0161. `SortBy` is `p := StdSort(p, (a: T, b: T) => e);` with a comparator, decision 0162. `Match` is a match over the enum with the key, decision 0109. `Pre` is a statement with the calls that run before it, decision
/// 0104. `SetOwnField` is `n := Some(n.value.(f := e));` of a local unique_ptr, decision 0186.
#[derive(PartialEq, Eq, Debug)]
pub enum DStmt {
    Return(DExpr),
    If(DExpr, Box<DStmts>, Box<DStmts>),
    Local(u32, DTy, DExpr),
    LocalCall(u32, DTy, u32, DArgs),
    ReturnCall(u32, DArgs),
    ReturnUpdate(Objs, u32, DArgs),
    Assign(u32, DExpr),
    AssignCall(u32, u32, DArgs),
    While(DExpr, DConds, DConds, Box<DStmts>),
    For(Box<DStmt>, u32, DExpr, DConds, DConds, Box<DStmts>, Box<DStmt>, u32),
    SetField(u32, DExpr),
    SetOut(u32, DExpr),
    SetOutField(u32, u32, DExpr),
    SetOwnField(u32, u32, DExpr),
    Update(Objs, u32, DArgs),
    UpdateAt(Obj, Box<DExpr>, Objs, u32, DArgs),
    LocalUpdate(u32, DTy, Objs, u32, DArgs),
    CallStmt(u32, DArgs),
    Exit,
    Assert(DExpr),
    Apply(u32, DArgs),
    Match(DExpr, u32, Box<DCases>),
    Pre(DCalls, Box<DStmt>),
    Sort(Box<DExpr>, DTy),
    SortBy(Box<DExpr>, u32, u32, DTy, Box<DExpr>),
    Moved(Box<DStmt>, Names),
    Gone(Box<DStmt>, u32, bool),
    Block(Box<DStmts>),
    DeclTemp(u32, DTy),
    AssignTemp(u32, DExpr),
    Scope(Box<DStmts>),
    Dtors(Box<DStmts>),
    SetResult(DExpr),
}

/// A place that a call writes back: a local by its name, the object of the member function that makes the call, or a reference
/// parameter of that function, decision 0108. `Owned` is the value of a local unique_ptr, which a virtual function writes, decision
/// 0169.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Obj {
    Local(u32),
    Object,
    Out(u32),
    Owned(u32),
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
/// id of its name, decision 0147. `Rounds` is a double operation that rounds. `Finite` is a double parameter, by the id of its name,
/// that no requires line says is finite, and `FiniteResult` is a trusted function that gives a double and no ensures line says
/// that it is finite, decision 0150. `VecLocal` is a local vector that is no copy of a vector in scope, and `PassLocal` is a local
/// vector that a call passes by reference, by the id of its name, decision 0160. `SortForm` is a `std::sort` with no rule,
/// decision 0161. `NoOverride` is a class with no override of a virtual function of its interface, or one with other parameters or
/// another result, and `Unchecked` is an override with no function in the model, each by the keys of the class and the interface,
/// the id of the name of the function and the line of the class. `NotFinal` is a class over an interface that is not final, by its
/// key and line. `IndexWritten` is a call through an element of a vector whose index reads a place that the call writes, by the line,
/// decision 0170. `Overload` is an interface with two virtual functions of one name, by its key and line, decision 0165. `Later` is
/// a contract of a virtual function that reads a virtual function declared after it, by the key of the interface, the ids of the
/// names of both functions and the line, decision 0166. `NoMethod` is an override that writes and has no method in the model, by
/// the keys of the class and the interface, the id of the name of the function and the line of the class, decision 0169.
/// `MoveRead` is a statement that moves a name and also reads it or moves it again, by the id of the name and the line, and `MovePlace` is a move in a place
/// with no rule, by the line, decision 0171. `ReadsOnly` is a call that changes a global that the caller lists on its reads line only,
/// by the id of the name of the callee, the id of the global and the line of the call. `GlobalClash` is a global that the function
/// lists with the name of a parameter or a local, by its id and the line. `MemberGlobal` is a member function that lists a global,
/// and `GlobalType` is a listed global of a type with no rule, each by the line that lists it, decision 0173. `SignedBits` is a
/// bit operator on a signed integer, and `ContractCast` is a cast in a contract that can change the value, each by the line.
/// `BraceLen` is a braced list of `m` values for a std::array of `n`, by `m`, `n` and the line, decision 0175. `TwoWrites` is an
/// expression with two writes where C++ fixes no order, by the line, `WriteRead` is one that writes a name and reads it elsewhere,
/// by the id of the name and the line, and `LoopWrite` is a write in the condition of a loop, by the line, decision 0177. `Copy`
/// is a copy of a struct with a destructor, and `NoDtorContract` is a local of a struct whose destructor has no contract, each by
/// the line, decision 0178.
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
    Rounds(u32),
    Finite(u32, u32),
    FiniteResult(u32),
    VecLocal(u32),
    PassLocal(u32, u32),
    SortForm(u32),
    NoOverride(u32, u32, u32, u32),
    Unchecked(u32, u32, u32, u32),
    NotFinal(u32, u32),
    Overload(u32, u32),
    Later(u32, u32, u32, u32),
    NoMethod(u32, u32, u32, u32),
    IndexWritten(u32),
    MoveRead(u32, u32),
    MovePlace(u32),
    ReadsOnly(u32, u32, u32),
    GlobalClash(u32, u32),
    MemberGlobal(u32),
    GlobalType(u32),
    SignedBits(u32),
    ContractCast(u32),
    BraceLen(u32, u32, u32),
    TwoWrites(u32),
    WriteRead(u32, u32),
    LoopWrite(u32),
    Copy(u32),
    NoDtorContract(u32),
}

// ------------------------------------------------------------------ the rules

/// The id of the name `operator()`. The shell gives this id to that text, decision 0098.
pub const CALL_OP: u32 = 0;

/// The id of the name `value`. The shell gives this id to that text, so `o.value()` on an object of a struct calls its member
/// `value`, decision 0169.
pub const VALUE_NAME: u32 = 1;

/// The id of the word `reads`. The shell gives this id to that text, so a reads line that names no global keeps the sentence of a
/// word with no rule, decision 0173.
pub const READS_NAME: u32 = 2;

/// The id of the name `count`. The shell gives this id to that text, so `a.count()` of a duration is its count, decision 0175.
pub const COUNT_NAME: u32 = 3;

/// The id of the name `~`, under which the table of structs lists the destructor of a struct. The shell gives this id to that text,
/// decision 0178.
pub const DTOR_NAME: u32 = 4;

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
        // A unique_ptr as an element of a vector, decision 0170.
        Scalar::Own(k) => DTy::Opt(Scalar::Struct(k)),
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
        Ty::F64 => Ok(DTy::Real),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        // A unique_ptr is a scalar of the model only as the element of a sequence, decision 0170.
        Ty::Opt(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Ptr(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Own(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Mut(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::MutAfter(Scalar::Own(_)) => Err(Refusal::Element(line)),
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
        Ty::Vec(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::Vec(s) => Ok(DTy::Seq(s)),
        Ty::Enum(k) => Ok(DTy::Enum(k)),
        // An interface is a type with no value that the model can see, decision 0165.
        Ty::Iface(k) => Ok(DTy::Iface(k)),
        Ty::IfaceRef(k) => Ok(DTy::Iface(k)),
        Ty::IfaceMut(k) => Ok(DTy::Iface(k)),
        Ty::Fresh(_) => Err(Refusal::Syntax(line)),
        Ty::Void => Err(Refusal::Syntax(line)),
        Ty::Other(k) => Err(Refusal::Construct(k, line)),
    }
}

/// A sort of a place whose elements are `s`, decision 0161. The default `<` is a strict weak order on integers only, so a vector of a
/// struct needs a comparator.
pub open spec fn spec_sort(p: DExpr, s: Scalar, line: u32) -> Result<DStmt, Refusal> {
    if s is Struct {
        Err(Refusal::SortForm(line))
    } else {
        Ok(DStmt::Sort(Box::new(p), spec_scalar_dty(s)))
    }
}

pub fn sort(p: DExpr, s: Scalar, line: u32) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_sort(p, s, line),
{
    if matches!(s, Scalar::Struct(_)) {
        Err(Refusal::SortForm(line))
    } else {
        Ok(DStmt::Sort(Box::new(p), scalar_dty(s)))
    }
}

/// A sort of a place whose elements are `s` with a comparator, decision 0162. Each parameter of the lambda has the element type, and
/// its test is code with no call. Dafny proves at the call that the comparator is a strict weak order.
pub open spec fn spec_sort_by(p: DExpr, s: Scalar, a: u32, b: u32, t: Ty, e: Expr, line: u32) -> Result<DStmt, Refusal> {
    if spec_elem(s) == t {
        match spec_ty(t, line) {
            Ok(dt) => match spec_code(e, line) {
                Ok(de) => Ok(DStmt::SortBy(Box::new(p), a, b, dt, Box::new(de))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        }
    } else {
        Err(Refusal::SortForm(line))
    }
}

pub fn sort_by(p: DExpr, s: Scalar, a: u32, b: u32, t: Ty, e: &Expr, line: u32) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_sort_by(p, s, a, b, t, *e, line),
{
    if elem(s) == t {
        match translate_ty(t, line) {
            Ok(dt) => match translate_code(e, line) {
                Ok(de) => Ok(DStmt::SortBy(Box::new(p), a, b, dt, Box::new(de))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        }
    } else {
        Err(Refusal::SortForm(line))
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
            // An interface is a parameter only, decision 0165.
            Ty::Iface(_) => Err(Refusal::Syntax(line)),
            Ty::IfaceRef(_) => Err(Refusal::Syntax(line)),
            Ty::IfaceMut(_) => Err(Refusal::Syntax(line)),
            // A struct that holds a sequence is a value, decision 0187. An optional of it stays out, decision 0137.
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
            // A local vector or a vector as a result, decisions 0160 and 0163.
            Ty::Vec(Scalar::Struct(k)) => if spec_holds(sd, k) {
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
        Scalar::Own(k) => Ty::Own(Scalar::Struct(k)),
    }
}

/// The scalar of the elements of a sequence parameter, read-only or written, decisions 0064 and 0145, or of a local vector, decision
/// 0160.
pub open spec fn spec_seq_elem(t: Ty) -> Option<Scalar> {
    match t {
        Ty::Seq(s, _) => Some(s),
        Ty::MutSeq(s) => Some(s),
        Ty::Vec(s) => Some(s),
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
        Ty::Vec(s) => Some(s),
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

/// An unsigned integer type, decision 0175.
pub open spec fn is_unsigned(t: Ty) -> bool {
    t == Ty::U8 || t == Ty::U16 || t == Ty::U32 || t == Ty::U64
}

/// A bit operator.
pub open spec fn is_bit_op(op: BinOp) -> bool {
    op == BinOp::BitAnd || op == BinOp::BitOr
}

/// `a & b` or `a | b` of code on the type `t`, decision 0175: the function of the prelude on both operands as exact integers, back
/// in `t`. Dafny proves that the value fits `t`. A signed type has no rule.
pub open spec fn spec_bits(op: BinOp, da: DExpr, db: DExpr, t: Ty, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !is_bit_op(op) {
            Err(Refusal::Syntax(line))
        } else if !is_unsigned(t) {
            Err(Refusal::SignedBits(line))
        } else {
            Ok(DExpr::Conv(dt, Box::new(DExpr::BitOp(op, Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db)))))))
        },
    }
}

/// An integral cast, decision 0058. Both types must be in the subset, and neither may be `bool`. The cast is `(e as T)`, so Dafny
/// proves that the value fits `T`, and the model never wraps.
/// A callee of the file that gives a double.
pub open spec fn spec_callee_real(all: Fns, k: u32) -> bool {
    match spec_find(all, k) {
        Some(f) => f.ret == Ty::F64,
        None => false,
    }
}

/// The exact double `m / q`: the quotient of two literals of the model, which does not round, decision 0158.
pub open spec fn spec_ratio(m: u64, q: u64) -> DExpr {
    DExpr::Bin(BinOp::Div, Box::new(DExpr::RealLit(m, 0)), Box::new(DExpr::RealLit(q, 0)))
}

pub fn ratio(m: u64, q: u64) -> (r: DExpr)
    ensures
        r == spec_ratio(m, q),
{
    DExpr::Bin(BinOp::Div, Box::new(DExpr::RealLit(m, 0)), Box::new(DExpr::RealLit(q, 0)))
}

/// An expression of code of type double, decision 0150. The forms that can give a double are a variable, a literal, a call, and
/// the forms around them.
pub open spec fn spec_real(e: Expr, all: Fns) -> bool
    decreases e,
{
    match e {
        Expr::Var(_, t) => t == Ty::F64,
        Expr::RealLit(_, _) => true,
        Expr::Ratio(_, _) => true,
        Expr::Neg(a) => spec_real(*a, all),
        Expr::Paren(a) => spec_real(*a, all),
        Expr::Brace(a) => spec_real(*a, all),
        // A conversion is of type double only when it gives a double, decision 0155.
        Expr::Cast(c, a) => match c {
            CastKind::Integral(_, to) => to == Ty::F64,
            CastKind::Other(_) => false,
            _ => spec_real(*a, all),
        },
        Expr::Cond(_, a, b) => spec_real(*a, all) || spec_real(*b, all),
        Expr::Bin(op, a, b) => spec_arith(op) && (spec_real(*a, all) || spec_real(*b, all)),
        Expr::Divide(_, _, _, t) => t == Ty::F64,
        Expr::Call(k, _, _, _) => spec_callee_real(all, k),
        _ => false,
    }
}

/// An operator of arithmetic, which rounds on a double.
pub open spec fn spec_arith(op: BinOp) -> bool {
    op == BinOp::Add || op == BinOp::Sub || op == BinOp::Mul || op == BinOp::Div || op == BinOp::Rem
}

pub fn arith(op: BinOp) -> (r: bool)
    ensures
        r == spec_arith(op),
{
    op == BinOp::Add || op == BinOp::Sub || op == BinOp::Mul || op == BinOp::Div || op == BinOp::Rem
}

pub fn callee_real(all: &Fns, k: u32) -> (r: bool)
    ensures
        r == spec_callee_real(*all, k),
{
    match find(all, k) {
        Some(f) => f.ret == Ty::F64,
        None => false,
    }
}

pub fn real(e: &Expr, all: &Fns) -> (r: bool)
    ensures
        r == spec_real(*e, *all),
    decreases e,
{
    match e {
        Expr::Var(_, t) => *t == Ty::F64,
        Expr::RealLit(_, _) => true,
        Expr::Ratio(_, _) => true,
        Expr::Neg(a) => real(a, all),
        Expr::Paren(a) => real(a, all),
        Expr::Brace(a) => real(a, all),
        Expr::Cast(c, a) => match c {
            CastKind::Integral(_, to) => *to == Ty::F64,
            CastKind::Other(_) => false,
            _ => real(a, all),
        },
        Expr::Cond(_, a, b) => real(a, all) || real(b, all),
        Expr::Bin(op, a, b) => arith(*op) && (real(a, all) || real(b, all)),
        Expr::Divide(_, _, _, t) => *t == Ty::F64,
        Expr::Call(k, _, _, _) => callee_real(all, *k),
        _ => false,
    }
}

pub open spec fn spec_integral(from: Ty, to: Ty, d: DExpr, line: u32) -> Result<DExpr, Refusal> {
    match spec_ty(from, line) {
        Err(r) => Err(r),
        Ok(_) => match spec_ty(to, line) {
            Err(r) => Err(r),
            // An integer converts to a double with `fint`, decision 0159.
            Ok(dto) => if to == Ty::F64 && from != Ty::Bool && from != Ty::F64 {
                Ok(DExpr::FromInt(Box::new(d)))
            } else if from == Ty::Bool || to == Ty::Bool || from == Ty::F64 || to == Ty::F64 {
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

/// The condition of a loop. It runs each turn, so no call runs before it, except a call of a const virtual function, which is its
/// function in place, decisions 0058 and 0172.
pub open spec fn spec_loop_test(e: Expr, all: Fns, line: u32, sd: Structs) -> Result<DExpr, Refusal> {
    match spec_lift(e, all, line, sd, 0, false) {
        Ok((_, d, _)) => Ok(d),
        Err(r) => Err(r),
    }
}

/// A statement with the calls that run before it. With no call it is the statement alone.
/// The value of a push_back. A value that the compiler turns into an optional, as `std::make_unique<D>(a)`, runs its calls before it,
/// decision 0170. Any other value is code with no call, decision 0148.
pub open spec fn spec_push_value(e: Expr, all: Fns, line: u32, sd: Structs) -> Result<(DCalls, DExpr), Refusal> {
    match e {
        Expr::Wrap(_) => match spec_lift(e, all, line, sd, 0, true) {
            Ok((c, d, _)) => Ok((c, d)),
            Err(r) => Err(r),
        },
        _ => match spec_code(e, line) {
            Ok(d) => Ok((List::Nil, d)),
            Err(r) => Err(r),
        },
    }
}

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
            // The std::array that a call gives is a temporary of the statement, decision 0175.
            Ty::Seq(_, Extent::Fixed(_)) => spec_ret_ty(f.ret, line, sd),
            _ => spec_value_ty(f.ret, line, sd),
        },
        None => Err(Refusal::Syntax(line)),
    }
}

/// The callee `key` is a const virtual function of an interface, a function of the model with no body. A call of it is that
/// function in any place of code, because it changes no state, decision 0172.
pub open spec fn spec_inline(all: Fns, key: u32) -> bool {
    match spec_find(all, key) {
        Some(f) => spec_const_virtual(f),
        None => false,
    }
}

pub fn inline(all: &Fns, key: u32) -> (r: bool)
    ensures
        r == spec_inline(*all, key),
{
    match find(all, key) {
        Some(f) => const_virtual(f),
        None => false,
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
        // A literal of type double, decision 0150.
        Expr::RealLit(d, k) => Ok((List::Nil, DExpr::RealLit(d, k), n)),
        Expr::Ratio(m, q) => Ok((List::Nil, spec_ratio(m, q), n)),
        Expr::Enumerator(k, i) => Ok((List::Nil, DExpr::Enumerator(k, i), n)),
        Expr::Var(v, t) => match spec_ty(t, line) {
            Ok(_) => Ok((List::Nil, spec_code_var(v, t), n)),
            Err(r) => Err(r),
        },
        // A call of a const virtual function of an interface is its function in place, decision 0172.
        Expr::Call(k, nm, args, at) => if spec_inline(all, k) && spec_callable(all, k, sd) {
            match spec_lift_args(*args, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => Ok((ca, DExpr::FCall(k, Box::new(da)), n1)),
            }
        } else if !open {
            Err(Refusal::Place(at))
        } else if !spec_callable(all, k, sd) {
            Err(Refusal::Callee(nm, at))
        } else if spec_callee_dtor(all, k, sd) {
            // A temporary of a struct with a destructor has no rule, decision 0178.
            Err(Refusal::Copy(line))
        } else {
            match spec_lift_args(*args, all, line, sd, n, open) {
                Err(r) => Err(r),
                // A call that gives no value stays alone, decision 0177. A refusal of an argument comes first.
                Ok((ca, da, n1)) => if spec_callee_void(all, k) { Err(Refusal::Place(at)) } else { match spec_callee_ty(all, k, line, sd) {
                    Err(r) => Err(r),
                    Ok(dt) => if n1 >= 0xFFFF_FFFF {
                        Err(Refusal::Syntax(line))
                    } else if spec_callee_writes(all, k) {
                        // A call that writes a value back runs first into a temporary, and writes its places, decision 0177. A
                        // call that gives no value stays alone.
                        if dt == DTy::Void {
                            Err(Refusal::Place(at))
                        } else {
                            match spec_free_callee_writebacks(all, k, *args, line) {
                                Err(r) => Err(r),
                                Ok(os) => Ok((spec_append(ca, List::Cons(DPre::Update(n1, dt, os, k, da), Box::new(List::Nil))), DExpr::Temp(n1), (n1 + 1) as u32)),
                            }
                        }
                    } else {
                        Ok((spec_append(ca, List::Cons(DPre::Call(n1, dt, k, da), Box::new(List::Nil))), DExpr::Temp(n1), (n1 + 1) as u32))
                    },
                } },
            }
        },
        // `x++` inside an expression writes first into a temporary, decision 0177. Where C++ may not run it, it has no place.
        Expr::Step(v, t, up, prefix) => if !open {
            Err(Refusal::Place(line))
        } else {
            match spec_step_ty(t) {
                None => Err(Refusal::Syntax(line)),
                Some(dt) => if n < 0xFFFF_FFFF {
                    Ok((List::Cons(DPre::Step(n, dt, v, up, prefix, t is Mut), Box::new(List::Nil)), DExpr::Temp(n), (n + 1) as u32))
                } else {
                    Err(Refusal::Syntax(line))
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
        // Arithmetic on a double is one rounding of the model, decision 0154. `%` has no rule, and the real model would make it
        // exact, decision 0150.
        Expr::Bin(op, a, b) => if spec_arith(op) && (spec_real(*a, all) || spec_real(*b, all)) {
            if op == BinOp::Rem || op == BinOp::Div {
                Err(Refusal::Rounds(line))
            } else {
                match spec_lift(*a, all, line, sd, n, open) {
                    Err(r) => Err(r),
                    Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open) {
                        Err(r) => Err(r),
                        Ok((cb, db, n2)) => Ok((spec_append(ca, cb), DExpr::FOp(op, Box::new(da), Box::new(db)), n2)),
                    },
                }
            }
        } else if op == BinOp::Div || op == BinOp::Rem || is_bit_op(op) || spec_ptr_var(*a) || spec_ptr_var(*b) {
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
        Expr::Divide(op, a, b, t) => if t == Ty::F64 || spec_real(*a, all) || spec_real(*b, all) {
            if op == BinOp::Div {
                match spec_lift(*a, all, line, sd, n, open) {
                    Err(r) => Err(r),
                    Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open) {
                        Err(r) => Err(r),
                        Ok((cb, db, n2)) => Ok((spec_append(ca, cb), DExpr::FOp(op, Box::new(da), Box::new(db)), n2)),
                    },
                }
            } else {
                Err(Refusal::Rounds(line))
            }
        } else if !(op == BinOp::Div || op == BinOp::Rem) {
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
        Expr::Bits(op, a, b, t) => match spec_lift(*a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match spec_lift(*b, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cb, db, n2)) => match spec_bits(op, da, db, t, line) {
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
            // A final class to its interface is the upcast of the model, decision 0166.
            CastKind::Upcast(dk, bk) => match spec_lift(*a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((c, d, n1)) => Ok((c, DExpr::Upcast(dk, bk, Box::new(d)), n1)),
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
        // A brace list of a struct with a destructor is a temporary, decision 0178.
        Expr::Construct(k, _) if spec_dtor_of(Ty::Struct(k), sd) is Some => Err(Refusal::Copy(line)),
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
        // A move that the statement did not take out stands in a place with no rule, decision 0171.
        Expr::Move(_, _) => Err(Refusal::MovePlace(line)),
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

/// `std::move(x)` stands where C++ makes a new `std::unique_ptr` from `x`: as the value itself, as an argument of a call or of a
/// constructor, or under a cast, a paren or the `Some` of `std::make_unique`, decision 0171. Each such move reads `x`. The names are
/// the moved names in their order. A move in any other place stays, and spec_lift refuses it.
pub open spec fn spec_unmove(e: Expr) -> (Expr, Names)
    decreases e,
{
    match e {
        Expr::Move(v, t) => (Expr::Var(v, t), List::Cons(v, Box::new(List::Nil))),
        Expr::Call(k, nm, args, at) => (Expr::Call(k, nm, Box::new(spec_unmove_args(*args).0), at), spec_unmove_args(*args).1),
        Expr::Construct(k, args) => (Expr::Construct(k, Box::new(spec_unmove_args(*args).0)), spec_unmove_args(*args).1),
        Expr::Wrap(a) => (Expr::Wrap(Box::new(spec_unmove(*a).0)), spec_unmove(*a).1),
        Expr::Cast(ck, a) => (Expr::Cast(ck, Box::new(spec_unmove(*a).0)), spec_unmove(*a).1),
        Expr::Paren(a) => (Expr::Paren(Box::new(spec_unmove(*a).0)), spec_unmove(*a).1),
        _ => (e, List::Nil),
    }
}

pub open spec fn spec_unmove_args(args: Args) -> (Args, Names)
    decreases args,
{
    match args {
        List::Nil => (List::Nil, List::Nil),
        List::Cons(a, rest) => (
            List::Cons(Box::new(spec_unmove(*a).0), Box::new(spec_unmove_args(*rest).0)),
            spec_append(spec_unmove(*a).1, spec_unmove_args(*rest).1),
        ),
    }
}

pub fn copy_expr(e: &Expr) -> (r: Expr)
    ensures
        r == *e,
    decreases e,
{
    match e {
        Expr::Int(f0) => Expr::Int(*f0),
        Expr::Lit(f0, f1) => Expr::Lit(*f0, *f1),
        Expr::Bool(f0) => Expr::Bool(*f0),
        Expr::Var(f0, f1) => Expr::Var(*f0, *f1),
        Expr::Name(f0) => Expr::Name(*f0),
        Expr::Result => Expr::Result,
        Expr::Bin(f0, f1, f2) => Expr::Bin(*f0, Box::new(copy_expr(f1)), Box::new(copy_expr(f2))),
        Expr::Not(f0) => Expr::Not(Box::new(copy_expr(f0))),
        Expr::Neg(f0) => Expr::Neg(Box::new(copy_expr(f0))),
        Expr::Cast(f0, f1) => Expr::Cast(*f0, Box::new(copy_expr(f1))),
        Expr::Paren(f0) => Expr::Paren(Box::new(copy_expr(f0))),
        Expr::Brace(f0) => Expr::Brace(Box::new(copy_expr(f0))),
        Expr::Call(f0, f1, f2, f3) => Expr::Call(*f0, *f1, Box::new(copy_args(f2)), *f3),
        Expr::Size(f0) => Expr::Size(Box::new(copy_expr(f0))),
        Expr::Index(f0, f1) => Expr::Index(Box::new(copy_expr(f0)), Box::new(copy_expr(f1))),
        Expr::Copy(f0, f1, f2) => Expr::Copy(Box::new(copy_expr(f0)), *f1, *f2),
        Expr::Field(f0, f1) => Expr::Field(Box::new(copy_expr(f0)), *f1),
        Expr::Construct(f0, f1) => Expr::Construct(*f0, Box::new(copy_args(f1))),
        Expr::Forall(f0, f1) => Expr::Forall(*f0, Box::new(copy_expr(f1))),
        Expr::Exists(f0, f1) => Expr::Exists(*f0, Box::new(copy_expr(f1))),
        Expr::Chain(f0, f1, f2, f3, f4) => Expr::Chain(*f0, *f1, Box::new(copy_expr(f2)), Box::new(copy_expr(f3)), Box::new(copy_expr(f4))),
        Expr::HasValue(f0) => Expr::HasValue(Box::new(copy_expr(f0))),
        Expr::Value(f0) => Expr::Value(Box::new(copy_expr(f0))),
        Expr::Nullopt => Expr::Nullopt,
        Expr::Wrap(f0) => Expr::Wrap(Box::new(copy_expr(f0))),
        Expr::Empty(f0) => Expr::Empty(Box::new(copy_expr(f0))),
        Expr::Subspan(f0, f1) => Expr::Subspan(Box::new(copy_expr(f0)), Box::new(copy_expr(f1))),
        Expr::Apply(f0, f1) => Expr::Apply(*f0, Box::new(copy_args(f1))),
        Expr::Suffix(f0, f1) => Expr::Suffix(Box::new(copy_expr(f0)), Box::new(copy_expr(f1))),
        Expr::Prefix(f0, f1) => Expr::Prefix(Box::new(copy_expr(f0)), Box::new(copy_expr(f1))),
        Expr::Slice(f0, f1, f2) => Expr::Slice(Box::new(copy_expr(f0)), Box::new(copy_expr(f1)), Box::new(copy_expr(f2))),
        Expr::Divide(f0, f1, f2, f3) => Expr::Divide(*f0, Box::new(copy_expr(f1)), Box::new(copy_expr(f2)), *f3),
        Expr::MApply(f0, f1, f2) => Expr::MApply(Box::new(copy_expr(f0)), *f1, Box::new(copy_args(f2))),
        Expr::Old(f0) => Expr::Old(Box::new(copy_expr(f0))),
        Expr::Cond(f0, f1, f2) => Expr::Cond(Box::new(copy_expr(f0)), Box::new(copy_expr(f1)), Box::new(copy_expr(f2))),
        Expr::Shr(f0, f1, f2) => Expr::Shr(Box::new(copy_expr(f0)), Box::new(copy_expr(f1)), *f2),
        Expr::Enumerator(f0, f1) => Expr::Enumerator(*f0, *f1),
        Expr::CountIf(f0, f1, f2, f3) => Expr::CountIf(Box::new(copy_expr(f0)), *f1, *f2, Box::new(copy_expr(f3))),
        Expr::RealLit(f0, f1) => Expr::RealLit(*f0, *f1),
        Expr::Ratio(f0, f1) => Expr::Ratio(*f0, *f1),
        Expr::Finite(f0) => Expr::Finite(Box::new(copy_expr(f0))),
        Expr::Abs(f0) => Expr::Abs(Box::new(copy_expr(f0))),
        Expr::Eps => Expr::Eps,
        Expr::Eta => Expr::Eta,
        Expr::DblMax => Expr::DblMax,
        Expr::EmptyVec => Expr::EmptyVec,
        Expr::Fill(f0, f1) => Expr::Fill(Box::new(copy_expr(f0)), Box::new(copy_expr(f1))),
        Expr::Unknown(f0, f1) => Expr::Unknown(*f0, *f1),
        Expr::Move(f0, f1) => Expr::Move(*f0, *f1),
        Expr::Bits(f0, f1, f2, f3) => Expr::Bits(*f0, Box::new(copy_expr(f1)), Box::new(copy_expr(f2)), *f3),
        Expr::StaticCast(f0, f1) => Expr::StaticCast(*f0, Box::new(copy_expr(f1))),
        Expr::List(f0) => Expr::List(Box::new(copy_args(f0))),
        Expr::Step(f0, f1, f2, f3) => Expr::Step(*f0, *f1, *f2, *f3),
    }
}

pub fn copy_args(args: &Args) -> (r: Args)
    ensures
        r == *args,
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => List::Cons(Box::new(copy_expr(a)), Box::new(copy_args(rest))),
    }
}

pub fn unmove(e: &Expr) -> (r: (Expr, Names))
    ensures
        r == spec_unmove(*e),
    decreases e,
{
    match e {
        Expr::Move(v, t) => (Expr::Var(*v, *t), List::Cons(*v, Box::new(List::Nil))),
        Expr::Call(k, nm, args, at) => {
            let (a, ns) = unmove_args(args);
            (Expr::Call(*k, *nm, Box::new(a), *at), ns)
        },
        Expr::Construct(k, args) => {
            let (a, ns) = unmove_args(args);
            (Expr::Construct(*k, Box::new(a)), ns)
        },
        Expr::Wrap(a) => {
            let (x, ns) = unmove(a);
            (Expr::Wrap(Box::new(x)), ns)
        },
        Expr::Cast(ck, a) => {
            let (x, ns) = unmove(a);
            (Expr::Cast(*ck, Box::new(x)), ns)
        },
        Expr::Paren(a) => {
            let (x, ns) = unmove(a);
            (Expr::Paren(Box::new(x)), ns)
        },
        _ => (copy_expr(e), List::Nil),
    }
}

pub fn unmove_args(args: &Args) -> (r: (Args, Names))
    ensures
        r == spec_unmove_args(*args),
    decreases args,
{
    match args {
        List::Nil => (List::Nil, List::Nil),
        List::Cons(a, rest) => {
            let (x, n1) = unmove(a);
            let (r, n2) = unmove_args(rest);
            (List::Cons(Box::new(x), Box::new(r)), append(n1, n2))
        },
    }
}

/// Each name that an expression reads, in any place, decision 0171. A move is no read here.
pub open spec fn spec_var_names(e: Expr) -> Names
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(f0, _) => List::Cons(f0, Box::new(List::Nil)),
        Expr::Name(f0) => List::Cons(f0, Box::new(List::Nil)),
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => spec_append(spec_var_names(*f1), spec_var_names(*f2)),
        Expr::Not(f0) => spec_var_names(*f0),
        Expr::Neg(f0) => spec_var_names(*f0),
        Expr::Cast(_, f1) => spec_var_names(*f1),
        Expr::Paren(f0) => spec_var_names(*f0),
        Expr::Brace(f0) => spec_var_names(*f0),
        Expr::Call(_, _, f2, _) => spec_var_names_args(*f2),
        Expr::Size(f0) => spec_var_names(*f0),
        Expr::Index(f0, f1) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Copy(f0, _, _) => spec_var_names(*f0),
        Expr::Field(f0, _) => spec_var_names(*f0),
        Expr::Construct(_, f1) => spec_var_names_args(*f1),
        Expr::Forall(_, f1) => spec_var_names(*f1),
        Expr::Exists(_, f1) => spec_var_names(*f1),
        Expr::Chain(_, _, f2, f3, f4) => spec_append(spec_var_names(*f2), spec_append(spec_var_names(*f3), spec_var_names(*f4))),
        Expr::HasValue(f0) => spec_var_names(*f0),
        Expr::Value(f0) => spec_var_names(*f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => spec_var_names(*f0),
        Expr::Empty(f0) => spec_var_names(*f0),
        Expr::Subspan(f0, f1) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Apply(_, f1) => spec_var_names_args(*f1),
        Expr::Suffix(f0, f1) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Prefix(f0, f1) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Slice(f0, f1, f2) => spec_append(spec_var_names(*f0), spec_append(spec_var_names(*f1), spec_var_names(*f2))),
        Expr::Divide(_, f1, f2, _) => spec_append(spec_var_names(*f1), spec_var_names(*f2)),
        Expr::MApply(f0, _, f2) => spec_append(spec_var_names(*f0), spec_var_names_args(*f2)),
        Expr::Old(f0) => spec_var_names(*f0),
        Expr::Cond(f0, f1, f2) => spec_append(spec_var_names(*f0), spec_append(spec_var_names(*f1), spec_var_names(*f2))),
        Expr::Shr(f0, f1, _) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Bits(_, f1, f2, _) => spec_append(spec_var_names(*f1), spec_var_names(*f2)),
        Expr::StaticCast(_, f1) => spec_var_names(*f1),
        Expr::List(f0) => spec_var_names_args(*f0),
        Expr::Step(f0, _, _, _) => List::Cons(f0, Box::new(List::Nil)),
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => spec_append(spec_var_names(*f0), spec_var_names(*f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => spec_var_names(*f0),
        Expr::Abs(f0) => spec_var_names(*f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => spec_append(spec_var_names(*f0), spec_var_names(*f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub open spec fn spec_var_names_args(args: Args) -> Names
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_var_names(*a), spec_var_names_args(*rest)),
    }
}

pub fn var_names(e: &Expr) -> (r: Names)
    ensures
        r == spec_var_names(*e),
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(f0, _) => List::Cons(*f0, Box::new(List::Nil)),
        Expr::Name(f0) => List::Cons(*f0, Box::new(List::Nil)),
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => append(var_names(f1), var_names(f2)),
        Expr::Not(f0) => var_names(f0),
        Expr::Neg(f0) => var_names(f0),
        Expr::Cast(_, f1) => var_names(f1),
        Expr::Paren(f0) => var_names(f0),
        Expr::Brace(f0) => var_names(f0),
        Expr::Call(_, _, f2, _) => var_names_args(f2),
        Expr::Size(f0) => var_names(f0),
        Expr::Index(f0, f1) => append(var_names(f0), var_names(f1)),
        Expr::Copy(f0, _, _) => var_names(f0),
        Expr::Field(f0, _) => var_names(f0),
        Expr::Construct(_, f1) => var_names_args(f1),
        Expr::Forall(_, f1) => var_names(f1),
        Expr::Exists(_, f1) => var_names(f1),
        Expr::Chain(_, _, f2, f3, f4) => append(var_names(f2), append(var_names(f3), var_names(f4))),
        Expr::HasValue(f0) => var_names(f0),
        Expr::Value(f0) => var_names(f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => var_names(f0),
        Expr::Empty(f0) => var_names(f0),
        Expr::Subspan(f0, f1) => append(var_names(f0), var_names(f1)),
        Expr::Apply(_, f1) => var_names_args(f1),
        Expr::Suffix(f0, f1) => append(var_names(f0), var_names(f1)),
        Expr::Prefix(f0, f1) => append(var_names(f0), var_names(f1)),
        Expr::Slice(f0, f1, f2) => append(var_names(f0), append(var_names(f1), var_names(f2))),
        Expr::Divide(_, f1, f2, _) => append(var_names(f1), var_names(f2)),
        Expr::MApply(f0, _, f2) => append(var_names(f0), var_names_args(f2)),
        Expr::Old(f0) => var_names(f0),
        Expr::Cond(f0, f1, f2) => append(var_names(f0), append(var_names(f1), var_names(f2))),
        Expr::Shr(f0, f1, _) => append(var_names(f0), var_names(f1)),
        Expr::Bits(_, f1, f2, _) => append(var_names(f1), var_names(f2)),
        Expr::StaticCast(_, f1) => var_names(f1),
        Expr::List(f0) => var_names_args(f0),
        Expr::Step(f0, _, _, _) => List::Cons(*f0, Box::new(List::Nil)),
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => append(var_names(f0), var_names(f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => var_names(f0),
        Expr::Abs(f0) => var_names(f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => append(var_names(f0), var_names(f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub fn var_names_args(args: &Args) -> (r: Names)
    ensures
        r == spec_var_names_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(var_names(a), var_names_args(rest)),
    }
}

/// The moves `ns` of one statement that reads the names `reads` besides, decision 0171. C++ does not fix the order of the
/// arguments of a call, so a statement that moves a name reads it nowhere else and moves it once. The parameters `ps` move only in a
/// return, because the model cannot write a parameter. A unique_ptr parameter that the body moves outside a return is a local of the
/// body and not in `ps`, decision 0186.
pub open spec fn spec_move_check(ns: Names, reads: Names, ps: Params, ret: bool, line: u32) -> Option<Refusal>
    decreases ns,
{
    match ns {
        List::Nil => None,
        List::Cons(v, rest) => if spec_has(*rest, v) || spec_has(reads, v) {
            Some(Refusal::MoveRead(v, line))
        } else if !ret && spec_get(ps, v) is Some {
            Some(Refusal::WriteParam(v, line))
        } else {
            spec_move_check(*rest, reads, ps, ret, line)
        },
    }
}

pub fn move_check(ns: &Names, reads: &Names, ps: &Params, ret: bool, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_move_check(*ns, *reads, *ps, ret, line),
    decreases ns,
{
    match ns {
        List::Nil => None,
        List::Cons(v, rest) => if has(rest, *v) || has(reads, *v) {
            Some(Refusal::MoveRead(*v, line))
        } else if !ret && get(ps, *v).is_some() {
            Some(Refusal::WriteParam(*v, line))
        } else {
            move_check(rest, reads, ps, ret, line)
        },
    }
}

/// A statement that moves the names `ns` sets each to null after it, decision 0171.
pub open spec fn spec_moved(d: DStmt, ns: Names) -> DStmt {
    match ns {
        List::Nil => d,
        _ => DStmt::Moved(Box::new(d), ns),
    }
}

pub fn moved(d: DStmt, ns: Names) -> (r: DStmt)
    ensures
        r == spec_moved(d, ns),
{
    match ns {
        List::Nil => d,
        _ => DStmt::Moved(Box::new(d), ns),
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
        Ty::Vec(s) => Ty::Seq(s, Extent::Dynamic),
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
/// An expression of a contract with a real in it: a double parameter or result, a decimal with a point, a word of a double bound,
/// an absolute value, or arithmetic on one of them, decision 0154. It is never true of an expression of integers alone, so `/` on
/// integers keeps the division of C++, decision 0088.
pub open spec fn spec_creal(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names) -> bool
    decreases e,
{
    match e {
        Expr::Name(n) => !spec_has(bound, n) && match spec_rebind(decl, ps, n) {
            Some((_, t)) => spec_view_ty(t) == Ty::F64,
            None => false,
        },
        Expr::Result => ret == Some(Ty::F64),
        Expr::RealLit(_, _) => true,
        Expr::Ratio(_, _) => true,
        Expr::Eps => true,
        Expr::Eta => true,
        Expr::DblMax => true,
        Expr::Abs(a) => spec_creal(*a, decl, ps, ret, bound),
        Expr::Paren(a) => spec_creal(*a, decl, ps, ret, bound),
        Expr::Neg(a) => spec_creal(*a, decl, ps, ret, bound),
        Expr::Old(a) => spec_creal(*a, decl, ps, ret, bound),
        Expr::Bin(op, a, b) => spec_arith(op) && (spec_creal(*a, decl, ps, ret, bound) || spec_creal(*b, decl, ps, ret, bound)),
        Expr::Cond(_, a, b) => spec_creal(*a, decl, ps, ret, bound) || spec_creal(*b, decl, ps, ret, bound),
        _ => false,
    }
}

pub fn creal(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names) -> (r: bool)
    ensures
        r == spec_creal(*e, *decl, *ps, ret, *bound),
    decreases e,
{
    match e {
        Expr::Name(n) => has(bound, *n) == false && match rebind(decl, ps, *n) {
            Some((_, t)) => view_ty(t) == Ty::F64,
            None => false,
        },
        Expr::Result => ret == Some(Ty::F64),
        Expr::RealLit(_, _) => true,
        Expr::Ratio(_, _) => true,
        Expr::Eps => true,
        Expr::Eta => true,
        Expr::DblMax => true,
        Expr::Abs(a) => creal(a, decl, ps, ret, bound),
        Expr::Paren(a) => creal(a, decl, ps, ret, bound),
        Expr::Neg(a) => creal(a, decl, ps, ret, bound),
        Expr::Old(a) => creal(a, decl, ps, ret, bound),
        Expr::Bin(op, a, b) => arith(*op) && (creal(a, decl, ps, ret, bound) || creal(b, decl, ps, ret, bound)),
        Expr::Cond(_, a, b) => creal(a, decl, ps, ret, bound) || creal(b, decl, ps, ret, bound),
        _ => false,
    }
}

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

/// An integer literal of a contract as a real, through a minus, decision 0158, and an integer leaf too, decision 0159. A contract
/// gives `Lit` only for a literal, `Bound` for a name that a quantifier binds, and `AsInt` only for a leaf: a name, a field,
/// `result`, an element, a value or a pure member call. Each is an exact integer. Parentheses give no node, so any other
/// expression stays as it is.
pub open spec fn spec_dreal(d: DExpr) -> DExpr
    decreases d,
{
    match d {
        DExpr::Lit(n) => DExpr::RealLit(n, 0),
        // An integer leaf or a bound name is its exact value, so as a real it is exact too, decision 0159.
        DExpr::AsInt(x) => DExpr::Conv(DTy::Real, Box::new(DExpr::AsInt(x))),
        DExpr::Bound(n) => DExpr::Conv(DTy::Real, Box::new(DExpr::Bound(n))),
        DExpr::Neg(x) => DExpr::Neg(Box::new(spec_dreal(*x))),
        _ => d,
    }
}

pub fn dreal(d: DExpr) -> (r: DExpr)
    ensures
        r == spec_dreal(d),
    decreases d,
{
    match d {
        DExpr::Lit(n) => DExpr::RealLit(n, 0),
        DExpr::AsInt(x) => DExpr::Conv(DTy::Real, Box::new(DExpr::AsInt(x))),
        DExpr::Bound(n) => DExpr::Conv(DTy::Real, Box::new(DExpr::Bound(n))),
        DExpr::Neg(x) => DExpr::Neg(Box::new(dreal(*x))),
        _ => d,
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
        // A decimal with a point is that real, and `std::isfinite` of a double is true in the model, which holds no NaN and no
        // infinity, decision 0150.
        Expr::RealLit(d, k) => Ok(DExpr::RealLit(d, k)),
        Expr::Ratio(m, q) => Ok(spec_ratio(m, q)),
        // The absolute value and the words of a double bound, decision 0154.
        // `|e|` of an integer is the absolute value of the integer, decision 0159.
        Expr::Abs(a) => match spec_contract(*a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(if spec_creal(*a, decl, ps, ret, bound) {
                DExpr::Abs(Box::new(da))
            } else {
                DExpr::IntAbs(Box::new(da))
            }),
            Err(r) => Err(r),
        },
        Expr::Eps => Ok(DExpr::Eps),
        Expr::Eta => Ok(DExpr::Eta),
        Expr::DblMax => Ok(DExpr::DblMax),
        Expr::Finite(a) => match spec_path(*a, decl, ps, ret, bound, line, sd) {
            Ok((_, t)) => if t == Ty::F64 {
                Ok(DExpr::Bool(true))
            } else {
                Err(Refusal::Syntax(line))
            },
            Err(r) => Err(r),
        },
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
        // `a & b` and `a | b` are the functions of the prelude on two naturals, decision 0175. A signed operand has no rule, and
        // neither has an operand that is true or false.
        Expr::Bin(op, a, b) if is_bit_op(op) => if spec_signed_operand(*a, decl, ps, ret, bound, line, sd) || spec_signed_operand(*b, decl, ps, ret, bound, line, sd) {
            Err(Refusal::SignedBits(line))
        } else if spec_boolish(*a) || spec_boolish(*b) {
            Err(Refusal::Syntax(line))
        } else {
            match spec_contract(*a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match spec_contract(*b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(DExpr::BitOp(op, Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        },
        // `static_cast<T>(e)` is the value of `e` when each value of its type fits `T`, decision 0175.
        Expr::StaticCast(t, a) => match *a {
            Expr::Int(v) => if is_integer(t) && v <= spec_max(t) {
                Ok(DExpr::Lit(v))
            } else {
                Err(Refusal::ContractCast(line))
            },
            _ => match spec_path(*a, decl, ps, ret, bound, line, sd) {
                Ok((d, at)) => if spec_fits(at, t) {
                    spec_leaf(d, at, line)
                } else {
                    Err(Refusal::ContractCast(line))
                },
                Err(Refusal::Syntax(_)) => Err(Refusal::ContractCast(line)),
                Err(r) => Err(r),
            },
        },
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
                    // `/` on reals is the real quotient, decision 0154.
                    // An integer literal next to a real is that real, decision 0158.
                    Ok(db) => {
                        let ra = spec_creal(*a, decl, ps, ret, bound);
                        let rb = spec_creal(*b, decl, ps, ret, bound);
                        let da = if rb { spec_dreal(da) } else { da };
                        let db = if ra { spec_dreal(db) } else { db };
                        Ok(if op == BinOp::Div && (ra || rb) {
                            DExpr::Bin(op, Box::new(da), Box::new(db))
                        } else {
                            spec_binary(op, da, db)
                        })
                    },
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
            // `o.value()` of an object of a struct calls its member `value`, decision 0169.
            Ok((d, t)) => match spec_struct_key(t) {
                Some(k) => match spec_member(sd, k, VALUE_NAME) {
                    Some((key, Some((rt, _)))) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(List::Nil)))), rt, line),
                    _ => Err(Refusal::NotPure(VALUE_NAME, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
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
                // A static member function, decision 0174, or a function of the companion file.
                None => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_static_value(f, da, *args, decl, ps, line, sd),
                    Err(r) => Err(r),
                },
            },
            None => if spec_fresh_member(ret, sd, f) {
                Err(Refusal::NoObject(f, line))
            } else {
                match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_static_value(f, da, *args, decl, ps, line, sd),
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
                // `a.count()` of a duration is its count, an int64, decision 0175.
                None => if f == COUNT_NAME && *args is Nil && t == Ty::I64 {
                    spec_leaf(d, t, line)
                } else {
                    Err(Refusal::Syntax(line))
                },
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
                        // A chain is two comparisons, so a literal next to a real in it is that real, decision 0158.
                        Ok(dc) => {
                            let rb = spec_creal(*b, decl, ps, ret, bound);
                            let da = if rb { spec_dreal(da) } else { da };
                            let dc = if rb { spec_dreal(dc) } else { dc };
                            let db = if spec_creal(*a, decl, ps, ret, bound) || spec_creal(*c, decl, ps, ret, bound) { spec_dreal(db) } else { db };
                            Ok(DExpr::Chain(o1, o2, Box::new(da), Box::new(db), Box::new(dc)))
                        },
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

/// An operand of a bit operator in a contract that is a signed integer, decision 0175.
pub open spec fn spec_signed_operand(e: Expr, decl: Names, ps: Params, ret: Option<Ty>, bound: Names, line: u32, sd: Structs) -> bool
    decreases e, 1nat,
{
    match spec_path(e, decl, ps, ret, bound, line, sd) {
        Ok((_, t)) => is_integer(t) && !is_unsigned(t),
        Err(_) => false,
    }
}

/// An operand that is true or false: a comparison, a logical operator, `!` or a literal of bool. C++ binds `==` tighter than `&`,
/// so `a & b == c` has such an operand.
pub open spec fn spec_boolish(e: Expr) -> bool {
    match e {
        Expr::Bin(op, _, _) => !spec_arith(op) && !is_bit_op(op),
        Expr::Chain(_, _, _, _, _) => true,
        Expr::Not(_) => true,
        Expr::Bool(_) => true,
        _ => false,
    }
}

/// The largest value of an integer type.
pub open spec fn spec_max(t: Ty) -> u64 {
    match t {
        Ty::U8 => 0xff,
        Ty::U16 => 0xffff,
        Ty::U32 => 0xffff_ffff,
        Ty::I8 => 0x7f,
        Ty::I16 => 0x7fff,
        Ty::I32 => 0x7fff_ffff,
        Ty::I64 => 0x7fff_ffff_ffff_ffff,
        _ => 0xffff_ffff_ffff_ffff,
    }
}

/// Each value of the integer type `from` is a value of the integer type `to`, decision 0175.
pub open spec fn spec_fits(from: Ty, to: Ty) -> bool {
    is_integer(from) && is_integer(to) && if is_unsigned(from) {
        if is_unsigned(to) { spec_width(from) <= spec_width(to) } else { spec_width(from) < spec_width(to) }
    } else {
        !is_unsigned(to) && spec_width(from) <= spec_width(to)
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
        // A vector as a result reads as a sequence, decision 0163.
        Expr::Result => match ret {
            Some(t) => Ok((DExpr::Result, spec_view_ty(t))),
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
            Ty::Iface(_) => Some((p, t)),
            Ty::IfaceMut(_) => Some((p, t)),
            _ => spec_self(*rest),
        },
        List::Nil => None,
    }
}

/// The function writes its object, decision 0096.
pub open spec fn spec_writes(ps: Params) -> bool {
    match spec_self(ps) {
        Some((_, Ty::ThisMut(_))) => true,
        Some((_, Ty::IfaceMut(_))) => true,
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
                Ty::IfaceMut(k) => Ty::ThisAfter(k),
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
        Ty::IfaceMut(_) => true,
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
            // The object of a virtual function of an interface, decision 0166.
            Ty::Iface(k) => Some((DExpr::Var(p), k)),
            Ty::IfaceMut(k) => Some((DExpr::Var(p), k)),
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

/// The type of the result of a function: a value type, `This` of a constructor, which can hold a sequence, decision 0187, or
/// `void`, decision 0096.
pub open spec fn spec_ret_ty(t: Ty, line: u32, sd: Structs) -> Result<DTy, Refusal> {
    match t {
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::Void => Ok(DTy::Void),
        // A std::array as a result is a sequence of its fixed extent, decision 0175.
        Ty::Seq(_, Extent::Fixed(_)) => spec_ty(t, line),
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
        // A vector by reference of a struct that holds a sequence, decision 0164.
        Ty::MutSeq(Scalar::Struct(k)) => if spec_holds(sd, k) {
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
        // A struct with a destructor by value is a copy, decision 0178.
        List::Cons((n, t), rest) => match (if spec_holds_dtor(t, sd) && !(t is Mut && t->Mut_0 is Struct) { Err(Refusal::Copy(line)) } else { spec_param_ty(t, line, sd) }) {
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
    spec_params(f.params, f.line, sd).is_ok() && spec_ret_ty(f.ret, f.line, sd).is_ok() && spec_checks(f) is None
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
        Stmt::SetOwnField(_, _, _, l) => l,
        Stmt::Switch(_, _, _, l) => l,
        Stmt::Call(_, _, _, l) => l,
        Stmt::Exit(l) => l,
        Stmt::Assert(_, l) => l,
        Stmt::Apply(_, _, l) => l,
        Stmt::SetIndex(_, _, _, l) => l,
        Stmt::SetFieldAt(_, _, _, l) => l,
        Stmt::PushBack(_, _, l) => l,
        Stmt::Sort(_, l) => l,
        Stmt::SortBy(_, _, _, _, _, l) => l,
        Stmt::Block(_, l) => l,
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
            CondKind::Reads => Err(Refusal::Misplaced(l)),
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
            // A call that passes a vector by reference on to a writer has no rule yet, decision 0147, nor one that passes a local
            // vector by reference, decision 0160.
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

/// The local unique_ptr whose value the expression reads: `*p` or `p->`, decision 0169.
pub open spec fn spec_owned(o: Expr) -> Option<u32>
    decreases o,
{
    match o {
        Expr::Value(a) => match *a {
            Expr::Var(v, t) => if t is Own {
                Some(v)
            } else {
                None
            },
            _ => None,
        },
        Expr::Cast(c, a) => if c == CastKind::Read || c == CastKind::NoOp {
            spec_owned(*a)
        } else {
            None
        },
        Expr::Paren(a) => spec_owned(*a),
        _ => None,
    }
}

/// The place that a call of a virtual function that writes its object writes back. It is a place of 0108, or the value of a local
/// unique_ptr of the interface, which takes the new value, decision 0169.
pub open spec fn spec_object_target(o: Expr, ps: Params, line: u32) -> Result<Obj, Refusal> {
    match spec_owned(o) {
        Some(v) => if spec_get(ps, v) is Some {
            Err(Refusal::NoTarget(line))
        } else {
            Ok(Obj::Owned(v))
        },
        None => spec_target(o, ps, line),
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
                match (if t is IfaceMut { spec_object_target(*a, ps, line) } else { spec_target(*a, ps, line) }) {
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

/// The place that an argument names, read from its type alone, for a call inside an expression, decision 0177. The check of the
/// statement, `spec_write_check`, has already found each place with the parameters, `spec_callee_writebacks`, so both agree.
pub open spec fn spec_free_target(o: Expr, line: u32) -> Result<Obj, Refusal>
    decreases o,
{
    match o {
        Expr::Var(v, t) => match t {
            Ty::ThisMut(_) => Ok(Obj::Object),
            Ty::Mut(_) => Ok(Obj::Out(v)),
            Ty::MutSeq(_) => Err(Refusal::PassOn(v, line)),
            _ => Ok(Obj::Local(v)),
        },
        Expr::Cast(c, a) => if c == CastKind::Read || c == CastKind::NoOp {
            spec_free_target(*a, line)
        } else {
            Err(Refusal::NoTarget(line))
        },
        Expr::Paren(a) => spec_free_target(*a, line),
        _ => Err(Refusal::NoTarget(line)),
    }
}

pub open spec fn spec_free_writebacks(args: Args, cps: Params, line: u32) -> Result<Objs, Refusal>
    decreases args,
{
    match args {
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match cps {
            List::Nil => Err(Refusal::Syntax(line)),
            List::Cons((_, t), crest) => if spec_written(t) {
                match (if t is IfaceMut {
                    match spec_owned(*a) {
                        Some(v) => Ok(Obj::Owned(v)),
                        None => spec_free_target(*a, line),
                    }
                } else {
                    spec_free_target(*a, line)
                }) {
                    Err(r) => Err(r),
                    Ok(o) => match spec_free_writebacks(*rest, *crest, line) {
                        Err(r) => Err(r),
                        Ok(os) => Ok(List::Cons(o, Box::new(os))),
                    },
                }
            } else {
                spec_free_writebacks(*rest, *crest, line)
            },
        },
    }
}

pub open spec fn spec_free_callee_writebacks(all: Fns, key: u32, args: Args, line: u32) -> Result<Objs, Refusal> {
    match spec_find(all, key) {
        Some(f) => spec_free_writebacks(args, f.params, line),
        None => Err(Refusal::Syntax(line)),
    }
}

/// The Dafny type of a name that a write inside an expression writes: an integer, or a reference parameter of one, decision 0177.
pub open spec fn spec_step_ty(t: Ty) -> Option<DTy> {
    match t {
        Ty::Mut(s) => match s {
            Scalar::Bool => None,
            Scalar::Struct(_) => None,
            Scalar::Own(_) => None,
            _ => Some(spec_scalar_dty(s)),
        },
        _ => spec_int_dty(t),
    }
}

/// A call that stands alone as a statement, decision 0096. A call of a function that gives back a value of a parameter writes each
/// such argument back, decision 0108. A call of any other function must give no value.
/// The element of a vector of unique_ptr that is the object of a call: `v[i]->f(a)`, by the name and type of the vector and the
/// index, decision 0170.
pub open spec fn spec_elem_object(o: Expr) -> Option<(u32, Ty, Expr)>
    decreases o,
{
    match o {
        Expr::Value(a) => match *a {
            Expr::Index(v, i) => match *v {
                Expr::Var(n, t) => match t {
                    Ty::Vec(Scalar::Own(_)) => Some((n, t, *i)),
                    Ty::MutSeq(Scalar::Own(_)) => Some((n, t, *i)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        Expr::Cast(c, a) => if c == CastKind::Read || c == CastKind::NoOp {
            spec_elem_object(*a)
        } else {
            None
        },
        Expr::Paren(a) => spec_elem_object(*a),
        _ => None,
    }
}

/// The place of a vector whose element a call writes back: a local vector, or a vector by reference on the modifies line.
pub open spec fn spec_vec_obj(v: u32, t: Ty, ps: Params, line: u32) -> Result<Obj, Refusal> {
    match t {
        Ty::Vec(_) => if spec_get(ps, v) is Some {
            Err(Refusal::NoTarget(line))
        } else {
            Ok(Obj::Local(v))
        },
        Ty::MutSeq(_) => if spec_get(ps, v) == Some(t) {
            Ok(Obj::Out(v))
        } else {
            Err(Refusal::NoTarget(line))
        },
        _ => Err(Refusal::NoTarget(line)),
    }
}

/// The names that an index reads, when it is names, literals, sizes and arithmetic. Any other index gives none.
pub open spec fn spec_index_vars(e: Expr) -> Option<Names>
    decreases e,
{
    match e {
        Expr::Var(n, _) => Some(List::Cons(n, Box::new(List::Nil))),
        Expr::Lit(_, _) => Some(List::Nil),
        Expr::Int(_) => Some(List::Nil),
        Expr::Cast(_, a) => spec_index_vars(*a),
        Expr::Paren(a) => spec_index_vars(*a),
        Expr::Size(a) => spec_index_vars(*a),
        Expr::Bin(_, a, b) => match spec_index_vars(*a) {
            Some(na) => match spec_index_vars(*b) {
                Some(nb) => Some(spec_append(na, nb)),
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

/// The place has a name in `ns`.
pub open spec fn spec_obj_named(o: Obj, ns: Names) -> bool {
    match o {
        Obj::Local(n) => spec_has(ns, n),
        Obj::Out(n) => spec_has(ns, n),
        Obj::Owned(n) => spec_has(ns, n),
        Obj::Object => false,
    }
}

/// A place that the call writes back has a name in `ns`.
pub open spec fn spec_writes_name(os: Objs, ns: Names) -> bool
    decreases os,
{
    match os {
        List::Nil => false,
        List::Cons(o, rest) => spec_obj_named(o, ns) || spec_writes_name(*rest, ns),
    }
}

/// A call of a virtual function that writes its object, whose object is an element of a vector of unique_ptr. It writes the new value
/// back to that element. The index reads no place that the call writes, decision 0170.
pub open spec fn spec_call_elem(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs) -> Option<Result<DStmt, Refusal>> {
    match spec_find(all, key) {
        Some(f) => if spec_head_ty(f.params) is Some && spec_head_ty(f.params)->Some_0 is IfaceMut {
            match args {
                List::Cons(a, rest) => match spec_elem_object(*a) {
                    Some((v, t, i)) => Some(match spec_vec_obj(v, t, ps, line) {
                        Err(r) => Err(r),
                        Ok(vo) => match spec_writebacks(*rest, spec_tail(f.params), ps, line) {
                            Err(r) => Err(r),
                            Ok(os) => match spec_index_vars(i) {
                                None => Err(Refusal::IndexWritten(line)),
                                Some(ns) => if spec_has(ns, v) || spec_writes_name(os, ns) {
                                    Err(Refusal::IndexWritten(line))
                                } else {
                                    match spec_code(i, line) {
                                        Err(r) => Err(r),
                                        Ok(di) => match spec_call_lift(key, name, args, line, all, line, sd) {
                                            Ok((c, da)) => Ok(spec_pre(c, DStmt::UpdateAt(vo, Box::new(di), os, key, da))),
                                            Err(r) => Err(r),
                                        },
                                    }
                                },
                            },
                        },
                    }),
                    None => None,
                },
                List::Nil => None,
            }
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn spec_call_stmt(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    // The value of the call is a temporary of a struct with a destructor, decision 0178.
    if spec_callee_dtor(all, key, sd) {
        Err(Refusal::Copy(line))
    } else if spec_callee_writes(all, key) && spec_call_elem(key, name, args, line, all, ps, sd) is Some {
        spec_call_elem(key, name, args, line, all, ps, sd)->Some_0
    } else if spec_callee_writes(all, key) {
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

/// The value of a return. A call gives its value to `result`, decision 0104. A call that writes a value back gives its value to
/// `result` and writes the value back, then returns, decision 0174.
pub open spec fn spec_return(e: Expr, l: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match e {
        Expr::Call(k, n, args, at) => if spec_callee_writes(all, k) {
            match spec_callee_writebacks(all, k, *args, ps, l) {
                Err(r) => Err(r),
                Ok(os) => match spec_call_lift(k, n, *args, at, all, l, sd) {
                    Ok((c, da)) => Ok(spec_pre(c, DStmt::ReturnUpdate(os, k, da))),
                    Err(r) => Err(r),
                },
            }
        } else {
            match spec_call_lift(k, n, *args, at, all, l, sd) {
                Ok((c, da)) => Ok(spec_pre(c, DStmt::ReturnCall(k, da))),
                Err(r) => Err(r),
            }
        },
        // `return {a, b, c};` of a std::array is the sequence of the values, decision 0175. The function checks the count first,
        // `spec_braces`.
        Expr::List(args) => match spec_lift_args(*args, all, l, sd, 0, true) {
            Ok((c, da, _)) => Ok(spec_pre(c, DStmt::Return(DExpr::SeqLit(Box::new(da))))),
            Err(r) => Err(r),
        },
        // The value of a return that builds the struct is the result itself, as in the body of a constructor. It is no temporary,
        // also for a struct with a destructor, decision 0178.
        Expr::Construct(k, args) => match spec_lift_args(*args, all, l, sd, 0, true) {
            Ok((c, da, _)) => Ok(spec_pre(c, DStmt::Return(DExpr::Ctor(k, Box::new(da))))),
            Err(r) => Err(r),
        },
        // A call or a write that C++ runs only sometimes makes the return statements of an if, decision 0177.
        _ => if spec_cond_calls(e, all, l, sd) {
            match spec_lower(e, None, false, all, l, sd, 0) {
                Ok((ss, _)) => Ok(DStmt::Block(Box::new(ss))),
                Err(r) => Err(r),
            }
        } else {
            match spec_lift(e, all, l, sd, 0, true) {
                Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Return(d))),
                Err(r) => Err(r),
            }
        },
    }
}

pub fn free_target(o: &Expr, line: u32) -> (r: Result<Obj, Refusal>)
    ensures
        r == spec_free_target(*o, line),
    decreases o,
{
    match o {
        Expr::Var(v, t) => match t {
            Ty::ThisMut(_) => Ok(Obj::Object),
            Ty::Mut(_) => Ok(Obj::Out(*v)),
            Ty::MutSeq(_) => Err(Refusal::PassOn(*v, line)),
            _ => Ok(Obj::Local(*v)),
        },
        Expr::Cast(c, a) => if *c == CastKind::Read || *c == CastKind::NoOp {
            free_target(a, line)
        } else {
            Err(Refusal::NoTarget(line))
        },
        Expr::Paren(a) => free_target(a, line),
        _ => Err(Refusal::NoTarget(line)),
    }
}

pub fn free_writebacks(args: &Args, cps: &Params, line: u32) -> (r: Result<Objs, Refusal>)
    ensures
        r == spec_free_writebacks(*args, *cps, line),
    decreases args,
{
    match args {
        List::Nil => Ok(List::Nil),
        List::Cons(a, rest) => match cps {
            List::Nil => Err(Refusal::Syntax(line)),
            List::Cons((_, t), crest) => if written(*t) {
                let o = if matches!(t, Ty::IfaceMut(_)) {
                    match owned(a) {
                        Some(v) => Ok(Obj::Owned(v)),
                        None => free_target(a, line),
                    }
                } else {
                    free_target(a, line)
                };
                match o {
                    Err(r) => Err(r),
                    Ok(o) => match free_writebacks(rest, crest, line) {
                        Err(r) => Err(r),
                        Ok(os) => Ok(List::Cons(o, Box::new(os))),
                    },
                }
            } else {
                free_writebacks(rest, crest, line)
            },
        },
    }
}

pub fn free_callee_writebacks(all: &Fns, key: u32, args: &Args, line: u32) -> (r: Result<Objs, Refusal>)
    ensures
        r == spec_free_callee_writebacks(*all, key, *args, line),
{
    match find(all, key) {
        Some(f) => free_writebacks(args, &f.params, line),
        None => Err(Refusal::Syntax(line)),
    }
}

pub fn step_ty(t: Ty) -> (r: Option<DTy>)
    ensures
        r == spec_step_ty(t),
{
    match t {
        Ty::Mut(s) => match s {
            Scalar::Bool => None,
            Scalar::Struct(_) => None,
            Scalar::Own(_) => None,
            _ => Some(scalar_dty(s)),
        },
        _ => int_dty(t),
    }
}

pub fn translate_return(e: &Expr, l: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_return(*e, l, *all, *ps, *sd),
{
    match e {
        Expr::Call(k, n, args, at) => if callee_writes(all, *k) {
            match callee_writebacks(all, *k, args, ps, l) {
                Err(r) => Err(r),
                Ok(os) => match call_lift(*k, *n, args, *at, all, l, sd) {
                    Ok((c, da)) => Ok(pre(c, DStmt::ReturnUpdate(os, *k, da))),
                    Err(r) => Err(r),
                },
            }
        } else {
            match call_lift(*k, *n, args, *at, all, l, sd) {
                Ok((c, da)) => Ok(pre(c, DStmt::ReturnCall(*k, da))),
                Err(r) => Err(r),
            }
        },
        Expr::List(args) => match lift_args(args, all, l, sd, 0, true) {
            Ok((c, da, _)) => Ok(pre(c, DStmt::Return(DExpr::SeqLit(Box::new(da))))),
            Err(r) => Err(r),
        },
        Expr::Construct(k, args) => match lift_args(args, all, l, sd, 0, true) {
            Ok((c, da, _)) => Ok(pre(c, DStmt::Return(DExpr::Ctor(*k, Box::new(da))))),
            Err(r) => Err(r),
        },
        _ => if cond_calls(e, all, l, sd) {
            match lower(e, None, false, all, l, sd, 0) {
                Ok((ss, _)) => Ok(DStmt::Block(Box::new(ss))),
                Err(r) => Err(r),
            }
        } else {
            match lift(e, all, l, sd, 0, true) {
                Ok((c, d, _)) => Ok(pre(c, DStmt::Return(d))),
                Err(r) => Err(r),
            }
        },
    }
}

/// The count of the values of a braced list, which stops at the largest u32.
pub open spec fn spec_count_args(args: Args) -> u32
    decreases args,
{
    match args {
        List::Nil => 0,
        List::Cons(_, rest) => {
            let c = spec_count_args(*rest);
            if c == u32::MAX { c } else { (c + 1) as u32 }
        },
    }
}

pub fn count_args(args: &Args) -> (r: u32)
    ensures
        r == spec_count_args(*args),
    decreases args,
{
    match args {
        List::Nil => 0,
        List::Cons(_, rest) => {
            let c = count_args(rest);
            if c == u32::MAX { c } else { c + 1 }
        },
    }
}

/// The fixed extent of a std::array result, decision 0175.
pub open spec fn spec_fixed(t: Ty) -> Option<u64> {
    match t {
        Ty::Seq(_, Extent::Fixed(k)) => Some(k),
        _ => None,
    }
}

pub fn fixed(t: Ty) -> (r: Option<u64>)
    ensures
        r == spec_fixed(t),
{
    match t {
        Ty::Seq(_, Extent::Fixed(k)) => Some(k),
        _ => None,
    }
}

/// The extent as a u32 for a refusal, which stops at the largest u32.
pub open spec fn spec_extent32(k: u64) -> u32 {
    if k > u32::MAX as u64 { u32::MAX } else { k as u32 }
}

pub fn extent32(k: u64) -> (r: u32)
    ensures
        r == spec_extent32(k),
{
    if k > u32::MAX as u64 { u32::MAX } else { k as u32 }
}

/// The first `return {...};` of a body whose count of values is not the extent `n` of the result, decision 0175. A braced list
/// is a value only for a std::array result.
pub open spec fn spec_brace_stmt(s: Stmt, n: Option<u64>) -> Option<Refusal>
    decreases s,
{
    match s {
        Stmt::Return(Expr::List(args), l) => match n {
            Some(k) => if spec_count_args(*args) as u64 == k {
                None
            } else {
                Some(Refusal::BraceLen(spec_count_args(*args), spec_extent32(k), l))
            },
            None => Some(Refusal::Syntax(l)),
        },
        Stmt::If(_, t, f, _) => match spec_braces(*t, n) {
            Some(r) => Some(r),
            None => spec_braces(*f, n),
        },
        Stmt::While(_, _, body, _) => spec_braces(*body, n),
        Stmt::For(_, _, _, _, body, _) => spec_braces(*body, n),
        Stmt::RangeFor(_, _, _, _, _, body, _) => spec_braces(*body, n),
        Stmt::Switch(_, _, cs, _) => spec_brace_cases(*cs, n),
        _ => None,
    }
}

pub open spec fn spec_braces(ss: Stmts, n: Option<u64>) -> Option<Refusal>
    decreases ss,
{
    match ss {
        List::Nil => None,
        List::Cons(s, rest) => match spec_brace_stmt(*s, n) {
            Some(r) => Some(r),
            None => spec_braces(*rest, n),
        },
    }
}

pub open spec fn spec_brace_cases(cs: Cases, n: Option<u64>) -> Option<Refusal>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => match spec_braces(*body, n) {
            Some(r) => Some(r),
            None => spec_brace_cases(*rest, n),
        },
    }
}

pub fn brace_stmt(s: &Stmt, n: Option<u64>) -> (r: Option<Refusal>)
    ensures
        r == spec_brace_stmt(*s, n),
    decreases s,
{
    match s {
        Stmt::Return(Expr::List(args), l) => match n {
            Some(k) => if count_args(args) as u64 == k {
                None
            } else {
                Some(Refusal::BraceLen(count_args(args), extent32(k), *l))
            },
            None => Some(Refusal::Syntax(*l)),
        },
        Stmt::If(_, t, f, _) => match braces(t, n) {
            Some(r) => Some(r),
            None => braces(f, n),
        },
        Stmt::While(_, _, body, _) => braces(body, n),
        Stmt::For(_, _, _, _, body, _) => braces(body, n),
        Stmt::RangeFor(_, _, _, _, _, body, _) => braces(body, n),
        Stmt::Switch(_, _, cs, _) => brace_cases(cs, n),
        _ => None,
    }
}

pub fn braces(ss: &Stmts, n: Option<u64>) -> (r: Option<Refusal>)
    ensures
        r == spec_braces(*ss, n),
    decreases ss,
{
    match ss {
        List::Nil => None,
        List::Cons(s, rest) => match brace_stmt(s, n) {
            Some(r) => Some(r),
            None => braces(rest, n),
        },
    }
}

pub fn brace_cases(cs: &Cases, n: Option<u64>) -> (r: Option<Refusal>)
    ensures
        r == spec_brace_cases(*cs, n),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((_, body), rest) => match braces(body, n) {
            Some(r) => Some(r),
            None => brace_cases(rest, n),
        },
    }
}

/// The ensures lines `ens`, after one for a std::array result: its length is the extent, decision 0175.
pub open spec fn spec_ret_len(t: Ty, line: u32, ens: DConds) -> DConds {
    match t {
        Ty::Seq(_, Extent::Fixed(k)) => List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Result))), Box::new(DExpr::Lit(k))), line), Box::new(ens)),
        _ => ens,
    }
}

pub fn ret_len(t: Ty, line: u32, ens: DConds) -> (r: DConds)
    ensures
        r == spec_ret_len(t, line, ens),
{
    match t {
        Ty::Seq(_, Extent::Fixed(k)) => List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(DExpr::Result))), Box::new(DExpr::Lit(k))), line), Box::new(ens)),
        _ => ens,
    }
}

// ------------------------------------------------------------------ a write inside an expression, decision 0177

/// A step before a statement that writes: an update or a step of a name.
pub open spec fn spec_pre_writes(p: DPre) -> bool {
    p is Update || p is Step
}

pub fn pre_writes(p: &DPre) -> (r: bool)
    ensures
        r == spec_pre_writes(*p),
{
    matches!(p, DPre::Update(..) | DPre::Step(..))
}

/// The count of the steps that write.
pub open spec fn spec_count_writes(c: DCalls) -> nat
    decreases c,
{
    match c {
        List::Nil => 0,
        List::Cons(p, rest) => (if spec_pre_writes(p) { 1nat } else { 0nat }) + spec_count_writes(*rest),
    }
}

/// More than one step writes.
pub open spec fn spec_writes_twice(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => if spec_pre_writes(p) {
            spec_any_write(*rest)
        } else {
            spec_writes_twice(*rest)
        },
    }
}

pub open spec fn spec_any_write(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => spec_pre_writes(p) || spec_any_write(*rest),
    }
}

pub fn writes_twice(c: &DCalls) -> (r: bool)
    ensures
        r == spec_writes_twice(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => if pre_writes(p) {
            any_write(rest)
        } else {
            writes_twice(rest)
        },
    }
}

pub fn any_write(c: &DCalls) -> (r: bool)
    ensures
        r == spec_any_write(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => pre_writes(p) || any_write(rest),
    }
}

/// Any step that writes a name with `x++`.
pub open spec fn spec_any_step(c: DCalls) -> bool
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => p is Step || spec_any_step(*rest),
    }
}

pub fn any_step(c: &DCalls) -> (r: bool)
    ensures
        r == spec_any_step(*c),
    decreases c,
{
    match c {
        List::Nil => false,
        List::Cons(p, rest) => matches!(p, DPre::Step(..)) || any_step(rest),
    }
}

/// The names of the places that the steps write.
pub open spec fn spec_obj_names(os: Objs) -> Names
    decreases os,
{
    match os {
        List::Nil => List::Nil,
        List::Cons(o, rest) => match o {
            Obj::Local(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Out(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Owned(v) => List::Cons(v, Box::new(spec_obj_names(*rest))),
            Obj::Object => spec_obj_names(*rest),
        },
    }
}

pub fn obj_names(os: &Objs) -> (r: Names)
    ensures
        r == spec_obj_names(*os),
    decreases os,
{
    match os {
        List::Nil => List::Nil,
        List::Cons(o, rest) => match o {
            Obj::Local(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Out(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Owned(v) => List::Cons(*v, Box::new(obj_names(rest))),
            Obj::Object => obj_names(rest),
        },
    }
}

pub open spec fn spec_written_names(c: DCalls) -> Names
    decreases c,
{
    match c {
        List::Nil => List::Nil,
        List::Cons(p, rest) => match p {
            DPre::Update(_, _, os, _, _) => spec_append(spec_obj_names(os), spec_written_names(*rest)),
            DPre::Step(_, _, v, _, _, _) => List::Cons(v, Box::new(spec_written_names(*rest))),
            DPre::Call(_, _, _, _) => spec_written_names(*rest),
        },
    }
}

pub fn written_names(c: &DCalls) -> (r: Names)
    ensures
        r == spec_written_names(*c),
    decreases c,
{
    match c {
        List::Nil => List::Nil,
        List::Cons(p, rest) => match p {
            DPre::Update(_, _, os, _, _) => append(obj_names(os), written_names(rest)),
            DPre::Step(_, _, v, _, _, _) => List::Cons(*v, Box::new(written_names(rest))),
            DPre::Call(_, _, _, _) => written_names(rest),
        },
    }
}

/// The name stands at least twice in the list.
pub open spec fn spec_has_twice(l: Names, x: u32) -> bool
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(h, t) => if h == x {
            spec_has(*t, x)
        } else {
            spec_has_twice(*t, x)
        },
    }
}

pub fn has_twice(l: &Names, x: u32) -> (r: bool)
    ensures
        r == spec_has_twice(*l, x),
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(h, t) => if *h == x {
            has(t, x)
        } else {
            has_twice(t, x)
        },
    }
}

/// The first written name that the region also reads elsewhere.
pub open spec fn spec_read_too(ws: Names, reads: Names, line: u32) -> Option<Refusal>
    decreases ws,
{
    match ws {
        List::Nil => None,
        List::Cons(x, rest) => if spec_has_twice(reads, x) {
            Some(Refusal::WriteRead(x, line))
        } else {
            spec_read_too(*rest, reads, line)
        },
    }
}

pub fn read_too(ws: &Names, reads: &Names, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_read_too(*ws, *reads, line),
    decreases ws,
{
    match ws {
        List::Nil => None,
        List::Cons(x, rest) => if has_twice(reads, *x) {
            Some(Refusal::WriteRead(*x, line))
        } else {
            read_too(rest, reads, line)
        },
    }
}

/// A place that a step writes and that the function cannot write: a reference parameter that is none, or a parameter by value.
pub open spec fn spec_bad_obj(o: Obj, ps: Params, line: u32) -> Option<Refusal> {
    match o {
        Obj::Out(v) => if spec_is_mut(ps, v) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Local(v) => if spec_get(ps, v) is Some { Some(Refusal::WriteParam(v, line)) } else { None },
        Obj::Object => if spec_writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Owned(v) => if spec_get(ps, v) is Some { Some(Refusal::NoTarget(line)) } else { None },
    }
}

pub fn bad_obj(o: Obj, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_obj(o, *ps, line),
{
    match o {
        Obj::Out(v) => if is_mut(ps, v) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Local(v) => if get(ps, v).is_some() { Some(Refusal::WriteParam(v, line)) } else { None },
        Obj::Object => if writes(ps) { None } else { Some(Refusal::Syntax(line)) },
        Obj::Owned(v) => if get(ps, v).is_some() { Some(Refusal::NoTarget(line)) } else { None },
    }
}

pub open spec fn spec_bad_objs(os: Objs, ps: Params, line: u32) -> Option<Refusal>
    decreases os,
{
    match os {
        List::Nil => None,
        List::Cons(o, rest) => match spec_bad_obj(o, ps, line) {
            Some(r) => Some(r),
            None => spec_bad_objs(*rest, ps, line),
        },
    }
}

pub fn bad_objs(os: &Objs, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_objs(*os, *ps, line),
    decreases os,
{
    match os {
        List::Nil => None,
        List::Cons(o, rest) => match bad_obj(*o, ps, line) {
            Some(r) => Some(r),
            None => bad_objs(rest, ps, line),
        },
    }
}

/// The first step that writes a place the function cannot write. The steps read each place from the type of the argument alone,
/// `spec_free_target`, so the parameters decide here.
pub open spec fn spec_bad_pres(c: DCalls, ps: Params, line: u32) -> Option<Refusal>
    decreases c,
{
    match c {
        List::Nil => None,
        List::Cons(p, rest) => match (match p {
            DPre::Update(_, _, os, _, _) => spec_bad_objs(os, ps, line),
            DPre::Step(_, _, v, _, _, out) => spec_bad_obj(if out { Obj::Out(v) } else { Obj::Local(v) }, ps, line),
            DPre::Call(_, _, _, _) => None,
        }) {
            Some(r) => Some(r),
            None => spec_bad_pres(*rest, ps, line),
        },
    }
}

pub fn bad_pres(c: &DCalls, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_bad_pres(*c, *ps, line),
    decreases c,
{
    match c {
        List::Nil => None,
        List::Cons(p, rest) => {
            let b = match p {
                DPre::Update(_, _, os, _, _) => bad_objs(os, ps, line),
                DPre::Step(_, _, v, _, _, out) => bad_obj(if *out { Obj::Out(*v) } else { Obj::Local(*v) }, ps, line),
                DPre::Call(_, _, _, _) => None,
            };
            match b {
                Some(r) => Some(r),
                None => bad_pres(rest, ps, line),
            }
        },
    }
}

/// The check of one region, where C++ fixes no order: each write goes to a place the function can write, at most one write
/// runs, and the name it writes is read nowhere else in the region. The region is lifted as the translation lifts it. A region
/// that does not lift has no check, because its translation refuses it.
pub open spec fn spec_check_region(e: Expr, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift(e, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match spec_bad_pres(c, ps, line) {
            Some(r) => Some(r),
            None => if spec_writes_twice(c) {
                Some(Refusal::TwoWrites(line))
            } else {
                spec_read_too(spec_written_names(c), spec_var_names(e), line)
            },
        },
    }
}

pub fn check_region(e: &Expr, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_region(*e, *all, *ps, *sd, line),
{
    match lift(e, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match bad_pres(&c, ps, line) {
            Some(r) => Some(r),
            None => if writes_twice(&c) {
                Some(Refusal::TwoWrites(line))
            } else {
                read_too(&written_names(&c), &var_names(e), line)
            },
        },
    }
}

/// The check of an expression: the sides of `&&` and `||`, and the condition and the branches of `?:`, are regions of their own,
/// because C++ runs them in order.
pub open spec fn spec_check_expr(e: Expr, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal>
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => if op == BinOp::And || op == BinOp::Or {
            match spec_check_expr(*a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => spec_check_expr(*b, all, ps, sd, line),
            }
        } else {
            spec_check_region(e, all, ps, sd, line)
        },
        Expr::Cond(c, a, b) => match spec_check_expr(*c, all, ps, sd, line) {
            Some(r) => Some(r),
            None => match spec_check_expr(*a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => spec_check_expr(*b, all, ps, sd, line),
            },
        },
        Expr::Paren(a) => spec_check_expr(*a, all, ps, sd, line),
        // The count and the value of `v(n, x)` are one region, as the arguments of a call are, decision 0185.
        Expr::Fill(c, x) => match spec_lift(*c, all, line, sd, 0, true) {
            Err(_) => None,
            Ok((c1, _, n1)) => match spec_lift(*x, all, line, sd, n1, true) {
                Err(_) => None,
                Ok((c2, _, _)) => spec_check_pres(spec_append(c1, c2), spec_var_names(e), ps, line),
            },
        },
        _ => spec_check_region(e, all, ps, sd, line),
    }
}

/// The checks of a region on the calls `c` that run before it, and the names `reads` that it reads, decision 0177.
pub open spec fn spec_check_pres(c: DCalls, reads: Names, ps: Params, line: u32) -> Option<Refusal> {
    match spec_bad_pres(c, ps, line) {
        Some(r) => Some(r),
        None => if spec_writes_twice(c) {
            Some(Refusal::TwoWrites(line))
        } else {
            spec_read_too(spec_written_names(c), reads, line)
        },
    }
}

pub fn check_pres(c: &DCalls, reads: &Names, ps: &Params, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_pres(*c, *reads, *ps, line),
{
    match bad_pres(c, ps, line) {
        Some(r) => Some(r),
        None => if writes_twice(c) {
            Some(Refusal::TwoWrites(line))
        } else {
            read_too(&written_names(c), reads, line)
        },
    }
}

pub fn check_expr(e: &Expr, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_expr(*e, *all, *ps, *sd, line),
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => if *op == BinOp::And || *op == BinOp::Or {
            match check_expr(a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => check_expr(b, all, ps, sd, line),
            }
        } else {
            check_region(e, all, ps, sd, line)
        },
        Expr::Cond(c, a, b) => match check_expr(c, all, ps, sd, line) {
            Some(r) => Some(r),
            None => match check_expr(a, all, ps, sd, line) {
                Some(r) => Some(r),
                None => check_expr(b, all, ps, sd, line),
            },
        },
        Expr::Paren(a) => check_expr(a, all, ps, sd, line),
        Expr::Fill(c, x) => match lift(c, all, line, sd, 0, true) {
            Err(_) => None,
            Ok((c1, _, n1)) => match lift(x, all, line, sd, n1, true) {
                Err(_) => None,
                Ok((c2, _, _)) => check_pres(&append(c1, c2), &var_names(e), ps, line),
            },
        },
        _ => check_region(e, all, ps, sd, line),
    }
}

/// A write in the condition of a loop, which runs at each turn, has no rule.
pub open spec fn spec_loop_write(c: Expr, all: Fns, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift(c, all, line, sd, 0, true) {
        Ok((cs, _, _)) => if spec_any_step(cs) { Some(Refusal::LoopWrite(line)) } else { None },
        Err(_) => None,
    }
}

pub fn loop_write(c: &Expr, all: &Fns, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_loop_write(*c, *all, *sd, line),
{
    match lift(c, all, line, sd, 0, true) {
        Ok((cs, _, _)) => if any_step(&cs) { Some(Refusal::LoopWrite(line)) } else { None },
        Err(_) => None,
    }
}

/// The check of the writes of a statement before it translates, decision 0177. A call that stands alone writes in its own body,
/// so only its arguments are a region. A statement with no expression of code has no check.
pub open spec fn spec_write_check(s: Stmt, all: Fns, ps: Params, sd: Structs) -> Option<Refusal>
    decreases s,
{
    match s {
        Stmt::Return(e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::Local(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::Assign(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetField(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetRefField(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetOwnField(_, _, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::PushBack(_, e, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::If(c, _, _, l) => spec_check_expr(c, all, ps, sd, l),
        Stmt::Switch(e, _, _, l) => spec_check_expr(e, all, ps, sd, l),
        Stmt::SetIndex(_, i, e, l) => match spec_check_expr(i, all, ps, sd, l) {
            Some(r) => Some(r),
            None => spec_check_expr(e, all, ps, sd, l),
        },
        Stmt::SetFieldAt(_, i, e, l) => match spec_check_expr(i, all, ps, sd, l) {
            Some(r) => Some(r),
            None => spec_check_expr(e, all, ps, sd, l),
        },
        Stmt::Call(_, _, args, l) => spec_check_args(*args, all, ps, sd, l),
        Stmt::While(c, _, _, l) => spec_loop_write(c, all, sd, l),
        Stmt::For(init, c, step, _, _, l) => match spec_write_check(*init, all, ps, sd) {
            Some(r) => Some(r),
            None => match spec_loop_write(c, all, sd, l) {
                Some(r) => Some(r),
                None => spec_write_check(*step, all, ps, sd),
            },
        },
        _ => None,
    }
}

/// The arguments of a call that stands alone, one region.
pub open spec fn spec_check_args(args: Args, all: Fns, ps: Params, sd: Structs, line: u32) -> Option<Refusal> {
    match spec_lift_args(args, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match spec_bad_pres(c, ps, line) {
            Some(r) => Some(r),
            None => if spec_writes_twice(c) {
                Some(Refusal::TwoWrites(line))
            } else {
                spec_read_too(spec_written_names(c), spec_var_names_args(args), line)
            },
        },
    }
}

pub fn check_args(args: &Args, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_check_args(*args, *all, *ps, *sd, line),
{
    match lift_args(args, all, line, sd, 0, true) {
        Err(_) => None,
        Ok((c, _, _)) => match bad_pres(&c, ps, line) {
            Some(r) => Some(r),
            None => if writes_twice(&c) {
                Some(Refusal::TwoWrites(line))
            } else {
                read_too(&written_names(&c), &var_names_args(args), line)
            },
        },
    }
}

pub fn write_check(s: &Stmt, all: &Fns, ps: &Params, sd: &Structs) -> (r: Option<Refusal>)
    ensures
        r == spec_write_check(*s, *all, *ps, *sd),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::Local(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::Assign(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetField(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetRefField(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetOwnField(_, _, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::PushBack(_, e, l) => check_expr(e, all, ps, sd, *l),
        Stmt::If(c, _, _, l) => check_expr(c, all, ps, sd, *l),
        Stmt::Switch(e, _, _, l) => check_expr(e, all, ps, sd, *l),
        Stmt::SetIndex(_, i, e, l) => match check_expr(i, all, ps, sd, *l) {
            Some(r) => Some(r),
            None => check_expr(e, all, ps, sd, *l),
        },
        Stmt::SetFieldAt(_, i, e, l) => match check_expr(i, all, ps, sd, *l) {
            Some(r) => Some(r),
            None => check_expr(e, all, ps, sd, *l),
        },
        Stmt::Call(_, _, args, l) => check_args(args, all, ps, sd, *l),
        Stmt::While(c, _, _, l) => loop_write(c, all, sd, *l),
        Stmt::For(init, c, step, _, _, l) => match write_check(init, all, ps, sd) {
            Some(r) => Some(r),
            None => match loop_write(c, all, sd, *l) {
                Some(r) => Some(r),
                None => write_check(step, all, ps, sd),
            },
        },
        _ => None,
    }
}

/// A part of an expression that runs a call or a write, or that the lift refuses as a call out of place.
pub open spec fn spec_needs_if(e: Expr, all: Fns, line: u32, sd: Structs) -> bool {
    match spec_lift(e, all, line, sd, 0, true) {
        Ok((c, _, _)) => !(c is Nil),
        Err(r) => r is Place,
    }
}

pub fn needs_if(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_needs_if(*e, *all, line, *sd),
{
    match lift(e, all, line, sd, 0, true) {
        Ok((c, _, _)) => !matches!(c, List::Nil),
        Err(r) => matches!(r, Refusal::Place(_)),
    }
}

/// An expression whose `&&` or `||` has a call or a write on its right side, or whose `?:` has one in a branch, at the top of the
/// expression. C++ runs such a part only sometimes.
pub open spec fn spec_cond_calls(e: Expr, all: Fns, line: u32, sd: Structs) -> bool
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => (op == BinOp::And || op == BinOp::Or) && (spec_needs_if(*b, all, line, sd) || spec_cond_calls(*a, all, line, sd)),
        Expr::Cond(_, a, b) => spec_needs_if(*a, all, line, sd) || spec_needs_if(*b, all, line, sd),
        Expr::Paren(a) => spec_cond_calls(*a, all, line, sd),
        _ => false,
    }
}

pub fn cond_calls(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_cond_calls(*e, *all, line, *sd),
    decreases e,
{
    match e {
        Expr::Bin(op, a, b) => (*op == BinOp::And || *op == BinOp::Or) && (needs_if(b, all, line, sd) || cond_calls(a, all, line, sd)),
        Expr::Cond(_, a, b) => needs_if(a, all, line, sd) || needs_if(b, all, line, sd),
        Expr::Paren(a) => cond_calls(a, all, line, sd),
        _ => false,
    }
}

/// The statement that takes the value of a part: the return, or the temporary `t`.
pub open spec fn spec_sink(sink: Option<u32>, res: bool, d: DExpr) -> DStmt {
    match sink {
        None => if res { DStmt::SetResult(d) } else { DStmt::Return(d) },
        Some(t) => DStmt::AssignTemp(t, d),
    }
}

pub fn sink_of(sink: Option<u32>, res: bool, d: DExpr) -> (r: DStmt)
    ensures
        r == spec_sink(sink, res, d),
{
    match sink {
        None => if res { DStmt::SetResult(d) } else { DStmt::Return(d) },
        Some(t) => DStmt::AssignTemp(t, d),
    }
}

/// A `return` whose `&&`, `||` or `?:` runs a call or a write only sometimes, as statements, decision 0177. `a && b` gives the
/// temporary `t` the value of `a`, then of `b` only when `t` holds. `a || b` runs `b` only when `t` does not hold. `c ? a : b`
/// gives each branch its own statements. The temporary takes its number before the calls of the left side. Each statement keeps
/// the place of the `return`.
pub open spec fn spec_lower(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32) -> Result<(DStmts, u32), Refusal>
    decreases e,
{
    match e {
        Expr::Paren(a) => spec_lower(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) {
            if n >= 0xFFFF_FFFF {
                Err(Refusal::Syntax(line))
            } else {
                let t = match sink { Some(t) => t, None => n };
                let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
                match spec_lower(*a, Some(t), res, all, line, sd, n0) {
                    Err(r) => Err(r),
                    Ok((sa, n1)) => match spec_lower(*b, Some(t), res, all, line, sd, n1) {
                        Err(r) => Err(r),
                        Ok((sb, n2)) => {
                            let test = if op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
                            let body = spec_append(sa, List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil)));
                            match sink {
                                Some(_) => Ok((body, n2)),
                                None => Ok((
                                    List::Cons((Box::new(DStmt::DeclTemp(t, DTy::Bool)), line), Box::new(spec_append(body, List::Cons((Box::new(spec_sink(None, res, DExpr::Temp(t))), line), Box::new(List::Nil))))),
                                    n2,
                                )),
                            }
                        },
                    },
                }
            }
        } else {
            spec_lower_leaf(e, sink, res, all, line, sd, n)
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            match spec_lift(*c, all, line, sd, n, true) {
                Err(r) => Err(r),
                Ok((cc, dc, n1)) => match spec_lower(*a, sink, res, all, line, sd, n1) {
                    Err(r) => Err(r),
                    Ok((sa, n2)) => match spec_lower(*b, sink, res, all, line, sd, n2) {
                        Err(r) => Err(r),
                        Ok((sb, n3)) => Ok((List::Cons((Box::new(spec_pre(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)))), line), Box::new(List::Nil)), n3)),
                    },
                },
            }
        } else {
            spec_lower_leaf(e, sink, res, all, line, sd, n)
        },
        _ => spec_lower_leaf(e, sink, res, all, line, sd, n),
    }
}

/// A part with no such `&&`, `||` or `?:` at its top: its calls run first, then the sink takes its value.
pub open spec fn spec_lower_leaf(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32) -> Result<(DStmts, u32), Refusal> {
    match spec_lift(e, all, line, sd, n, true) {
        Err(r) => Err(r),
        Ok((c, d, n1)) => Ok((List::Cons((Box::new(spec_pre(c, spec_sink(sink, res, d))), line), Box::new(List::Nil)), n1)),
    }
}

pub fn lower_leaf(e: &Expr, sink: Option<u32>, res: bool, all: &Fns, line: u32, sd: &Structs, n: u32) -> (r: Result<(DStmts, u32), Refusal>)
    ensures
        r == spec_lower_leaf(*e, sink, res, *all, line, *sd, n),
{
    match lift(e, all, line, sd, n, true) {
        Err(r) => Err(r),
        Ok((c, d, n1)) => Ok((List::Cons((Box::new(pre(c, sink_of(sink, res, d))), line), Box::new(List::Nil)), n1)),
    }
}

pub fn lower(e: &Expr, sink: Option<u32>, res: bool, all: &Fns, line: u32, sd: &Structs, n: u32) -> (r: Result<(DStmts, u32), Refusal>)
    ensures
        r == spec_lower(*e, sink, res, *all, line, *sd, n),
    decreases e,
{
    match e {
        Expr::Paren(a) => lower(a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (*op == BinOp::And || *op == BinOp::Or) && cond_calls(e, all, line, sd) {
            if n >= 0xFFFF_FFFF {
                Err(Refusal::Syntax(line))
            } else {
                let t = match sink { Some(t) => t, None => n };
                let n0: u32 = if sink.is_none() { n + 1 } else { n };
                match lower(a, Some(t), res, all, line, sd, n0) {
                    Err(r) => Err(r),
                    Ok((sa, n1)) => match lower(b, Some(t), res, all, line, sd, n1) {
                        Err(r) => Err(r),
                        Ok((sb, n2)) => {
                            let test = if *op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
                            let body = append(sa, List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil)));
                            match sink {
                                Some(_) => Ok((body, n2)),
                                None => Ok((
                                    List::Cons((Box::new(DStmt::DeclTemp(t, DTy::Bool)), line), Box::new(append(body, List::Cons((Box::new(sink_of(None, res, DExpr::Temp(t))), line), Box::new(List::Nil))))),
                                    n2,
                                )),
                            }
                        },
                    },
                }
            }
        } else {
            lower_leaf(e, sink, res, all, line, sd, n)
        },
        Expr::Cond(c, a, b) => if cond_calls(e, all, line, sd) {
            match lift(c, all, line, sd, n, true) {
                Err(r) => Err(r),
                Ok((cc, dc, n1)) => match lower(a, sink, res, all, line, sd, n1) {
                    Err(r) => Err(r),
                    Ok((sa, n2)) => match lower(b, sink, res, all, line, sd, n2) {
                        Err(r) => Err(r),
                        Ok((sb, n3)) => Ok((List::Cons((Box::new(pre(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)))), line), Box::new(List::Nil)), n3)),
                    },
                },
            }
        } else {
            lower_leaf(e, sink, res, all, line, sd, n)
        },
        _ => lower_leaf(e, sink, res, all, line, sd, n),
    }
}

/// Each call of a lowered `return` names a key with a method.
pub proof fn lemma_lower_resolves(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lower(e, sink, res, all, line, sd, n).is_ok(),
    ensures
        calls_resolve(spec_lower(e, sink, res, all, line, sd, n).unwrap().0, all, sd),
    decreases e,
{
    reveal_with_fuel(calls_resolve, 3);
    match e {
        Expr::Paren(a) => lemma_lower_resolves(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) {
            let t = match sink { Some(t) => t, None => n };
            let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
            lemma_lower_resolves(*a, Some(t), res, all, line, sd, n0);
            let (sa, n1) = spec_lower(*a, Some(t), res, all, line, sd, n0).unwrap();
            lemma_lower_resolves(*b, Some(t), res, all, line, sd, n1);
            let (sb, _) = spec_lower(*b, Some(t), res, all, line, sd, n1).unwrap();
            let test = if op == BinOp::And { DExpr::Temp(t) } else { DExpr::Not(Box::new(DExpr::Temp(t))) };
            let tail = List::Cons((Box::new(DStmt::If(test, Box::new(sb), Box::new(List::Nil))), line), Box::new(List::Nil));
            lemma_resolve_append(sa, tail, all, sd);
            let body = spec_append(sa, tail);
            let ret = List::Cons((Box::new(spec_sink(None, res, DExpr::Temp(t))), line), Box::new(List::Nil));
            lemma_resolve_append(body, ret, all, sd);
        } else {
            lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n);
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            lemma_lift_resolves(*c, all, line, sd, n, true);
            let (cc, dc, n1) = spec_lift(*c, all, line, sd, n, true).unwrap();
            lemma_lower_resolves(*a, sink, res, all, line, sd, n1);
            let (sa, n2) = spec_lower(*a, sink, res, all, line, sd, n1).unwrap();
            lemma_lower_resolves(*b, sink, res, all, line, sd, n2);
            let (sb, _) = spec_lower(*b, sink, res, all, line, sd, n2).unwrap();
            lemma_pre_resolves(cc, DStmt::If(dc, Box::new(sa), Box::new(sb)), all, sd);
        } else {
            lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n);
        },
        _ => lemma_lower_leaf_resolves(e, sink, res, all, line, sd, n),
    }
}

pub proof fn lemma_lower_leaf_resolves(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        spec_lower_leaf(e, sink, res, all, line, sd, n).is_ok(),
    ensures
        calls_resolve(spec_lower_leaf(e, sink, res, all, line, sd, n).unwrap().0, all, sd),
{
    reveal_with_fuel(calls_resolve, 2);
    lemma_lift_resolves(e, all, line, sd, n, true);
    let (c, d, _) = spec_lift(e, all, line, sd, n, true).unwrap();
    lemma_pre_resolves(c, spec_sink(sink, res, d), all, sd);
}

/// The calls of two lists of statements resolve when the calls of each do.
pub proof fn lemma_resolve_append(a: DStmts, b: DStmts, all: Fns, sd: Structs)
    ensures
        calls_resolve(spec_append(a, b), all, sd) == (calls_resolve(a, all, sd) && calls_resolve(b, all, sd)),
    decreases a,
{
    match a {
        List::Nil => {},
        List::Cons(_, rest) => lemma_resolve_append(*rest, b, all, sd),
    }
}

/// A lowered `return` with a node that has no rule is refused.
pub proof fn lemma_unknown_lower_is_refused(e: Expr, sink: Option<u32>, res: bool, all: Fns, line: u32, sd: Structs, n: u32)
    requires
        unknown_expr(e),
    ensures
        spec_lower(e, sink, res, all, line, sd, n).is_err(),
    decreases e,
{
    match e {
        Expr::Paren(a) => lemma_unknown_lower_is_refused(*a, sink, res, all, line, sd, n),
        Expr::Bin(op, a, b) => if (op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd) && n < 0xFFFF_FFFF {
            let t = match sink { Some(t) => t, None => n };
            let n0: u32 = if sink is None { (n + 1) as u32 } else { n };
            if unknown_expr(*a) {
                lemma_unknown_lower_is_refused(*a, Some(t), res, all, line, sd, n0);
            } else if spec_lower(*a, Some(t), res, all, line, sd, n0).is_ok() {
                lemma_unknown_lower_is_refused(*b, Some(t), res, all, line, sd, spec_lower(*a, Some(t), res, all, line, sd, n0).unwrap().1);
            }
        } else if !((op == BinOp::And || op == BinOp::Or) && spec_cond_calls(e, all, line, sd)) {
            lemma_unknown_lift_is_refused(e, all, line, sd, n, true);
        },
        Expr::Cond(c, a, b) => if spec_cond_calls(e, all, line, sd) {
            if unknown_expr(*c) {
                lemma_unknown_lift_is_refused(*c, all, line, sd, n, true);
            } else if spec_lift(*c, all, line, sd, n, true).is_ok() {
                let n1 = spec_lift(*c, all, line, sd, n, true).unwrap().2;
                if unknown_expr(*a) {
                    lemma_unknown_lower_is_refused(*a, sink, res, all, line, sd, n1);
                } else if spec_lower(*a, sink, res, all, line, sd, n1).is_ok() {
                    lemma_unknown_lower_is_refused(*b, sink, res, all, line, sd, spec_lower(*a, sink, res, all, line, sd, n1).unwrap().1);
                }
            }
        } else {
            lemma_unknown_lift_is_refused(e, all, line, sd, n, true);
        },
        _ => lemma_unknown_lift_is_refused(e, all, line, sd, n, true),
    }
}

// ------------------------------------------------------------------ a struct with a destructor, decision 0178

/// The key of the destructor of the struct of a type: a value of a struct of the file whose table lists a destructor.
pub open spec fn spec_dtor_of(t: Ty, sd: Structs) -> Option<u32> {
    match t {
        Ty::Struct(k) => match spec_member(sd, k, DTOR_NAME) {
            Some((key, _)) => Some(key),
            None => None,
        },
        _ => None,
    }
}

pub fn dtor_of(t: Ty, sd: &Structs) -> (r: Option<u32>)
    ensures
        r == spec_dtor_of(t, *sd),
{
    match t {
        Ty::Struct(k) => match member(sd, k, DTOR_NAME) {
            Some((key, _)) => Some(key),
            None => None,
        },
        _ => None,
    }
}

/// A type that holds a struct with a destructor: the struct itself, a reference to it, or a sequence, an optional, a pointer or a
/// unique_ptr of it, decision 0178.
pub open spec fn spec_holds_dtor(t: Ty, sd: Structs) -> bool {
    match t {
        Ty::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        Ty::Seq(s, _) => spec_scalar_dtor(s, sd),
        Ty::Vec(s) => spec_scalar_dtor(s, sd),
        Ty::MutSeq(s) => spec_scalar_dtor(s, sd),
        Ty::MutSeqAfter(s) => spec_scalar_dtor(s, sd),
        Ty::Opt(s) => spec_scalar_dtor(s, sd),
        Ty::Own(s) => spec_scalar_dtor(s, sd),
        Ty::Ptr(s) => spec_scalar_dtor(s, sd),
        Ty::Mut(s) => spec_scalar_dtor(s, sd),
        Ty::MutAfter(s) => spec_scalar_dtor(s, sd),
        _ => false,
    }
}

pub open spec fn spec_scalar_dtor(s: Scalar, sd: Structs) -> bool {
    match s {
        Scalar::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        Scalar::Own(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
        _ => false,
    }
}

pub fn scalar_dtor(s: Scalar, sd: &Structs) -> (r: bool)
    ensures
        r == spec_scalar_dtor(s, *sd),
{
    match s {
        Scalar::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        Scalar::Own(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        _ => false,
    }
}

pub fn holds_dtor(t: Ty, sd: &Structs) -> (r: bool)
    ensures
        r == spec_holds_dtor(t, *sd),
{
    match t {
        Ty::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
        Ty::Seq(s, _) => scalar_dtor(s, sd),
        Ty::Vec(s) => scalar_dtor(s, sd),
        Ty::MutSeq(s) => scalar_dtor(s, sd),
        Ty::MutSeqAfter(s) => scalar_dtor(s, sd),
        Ty::Opt(s) => scalar_dtor(s, sd),
        Ty::Own(s) => scalar_dtor(s, sd),
        Ty::Ptr(s) => scalar_dtor(s, sd),
        Ty::Mut(s) => scalar_dtor(s, sd),
        Ty::MutAfter(s) => scalar_dtor(s, sd),
        _ => false,
    }
}

/// The locals of a scope whose type has a destructor, the newest first, which is the order in which they die.
pub open spec fn spec_live(env: Params, sd: Structs) -> Params
    decreases env,
{
    match env {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if spec_dtor_of(t, sd) is Some {
            List::Cons((n, t), Box::new(spec_live(*rest, sd)))
        } else {
            spec_live(*rest, sd)
        },
    }
}

pub fn live(env: &Params, sd: &Structs) -> (r: Params)
    ensures
        r == spec_live(*env, *sd),
    decreases env,
{
    match env {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if dtor_of(*t, sd).is_some() {
            List::Cons((*n, *t), Box::new(live(rest, sd)))
        } else {
            live(rest, sd)
        },
    }
}

/// The locals that the statements of a block declare at its top, the newest first, after the locals `acc`.
pub open spec fn spec_block_locals(ss: Stmts, acc: Params) -> Params
    decreases ss,
{
    match ss {
        List::Nil => acc,
        List::Cons(s, rest) => spec_block_locals(*rest, spec_scope(*s, acc)),
    }
}

pub fn block_locals(ss: &Stmts, acc: Params) -> (r: Params)
    ensures
        r == spec_block_locals(*ss, acc),
    decreases ss,
{
    match ss {
        List::Nil => acc,
        List::Cons(s, rest) => block_locals(rest, scope(s, &acc)),
    }
}

/// The last statement of a block is a return or an exit, so nothing runs at the end of the block.
pub open spec fn spec_ends_out(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => if *rest is Nil {
            *s is Return || *s is Exit
        } else {
            spec_ends_out(*rest)
        },
    }
}

pub fn ends_out(ss: &Stmts) -> (r: bool)
    ensures
        r == spec_ends_out(*ss),
    decreases ss,
{
    match ss {
        List::Nil => false,
        List::Cons(s, rest) => if matches!(**rest, List::Nil) {
            matches!(**s, Stmt::Return(..) | Stmt::Exit(..))
        } else {
            ends_out(rest)
        },
    }
}

/// The place of the last statement of a block.
pub open spec fn spec_last_place(ss: Stmts) -> u32
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons(s, rest) => if *rest is Nil {
            spec_place(*s)
        } else {
            spec_last_place(*rest)
        },
    }
}

pub fn last_place(ss: &Stmts) -> (r: u32)
    ensures
        r == spec_last_place(*ss),
    decreases ss,
{
    match ss {
        List::Nil => 0,
        List::Cons(s, rest) => if matches!(**rest, List::Nil) {
            place(s)
        } else {
            last_place(rest)
        },
    }
}

/// The arguments for the globals of a destructor: each is the parameter of the caller with the name of the global. A caller
/// that does not list the global gives the name, which the translation refuses.
pub open spec fn spec_dtor_globals(dps: Params, ps: Params) -> Args
    decreases dps,
{
    match dps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(
            Box::new(match spec_get(ps, g) {
                Some(t) => Expr::Var(g, t),
                None => Expr::Name(g),
            }),
            Box::new(spec_dtor_globals(*rest, ps)),
        ),
    }
}

pub fn dtor_globals(dps: &Params, ps: &Params) -> (r: Args)
    ensures
        r == spec_dtor_globals(*dps, *ps),
    decreases dps,
{
    match dps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(
            Box::new(match get(ps, *g) {
                Some(t) => Expr::Var(*g, t),
                None => Expr::Name(*g),
            }),
            Box::new(dtor_globals(rest, ps)),
        ),
    }
}

/// The call of the destructor of the local `v` of type `t`, as a call that stands alone: the local as its object, then its
/// globals.
pub open spec fn spec_dtor_call(v: u32, t: Ty, all: Fns, ps: Params, sd: Structs, line: u32) -> Result<DStmt, Refusal> {
    match spec_dtor_of(t, sd) {
        None => Err(Refusal::Syntax(line)),
        Some(key) => match spec_find(all, key) {
            None => Err(Refusal::Syntax(line)),
            Some(f) => spec_call_stmt(key, DTOR_NAME, List::Cons(Box::new(Expr::Var(v, t)), Box::new(spec_dtor_globals(spec_tail(f.params), ps))), line, all, ps, sd),
        },
    }
}

pub fn dtor_call(v: u32, t: Ty, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dtor_call(v, t, *all, *ps, *sd, line),
{
    match dtor_of(t, sd) {
        None => Err(Refusal::Syntax(line)),
        Some(key) => match find(all, key) {
            None => Err(Refusal::Syntax(line)),
            Some(f) => {
                let args = List::Cons(Box::new(Expr::Var(v, t)), Box::new(dtor_globals(&tail(&f.params), ps)));
                call_stmt(key, DTOR_NAME, &args, line, all, ps, sd)
            },
        },
    }
}

/// The calls of the destructors of the locals `ls`, in their order.
pub open spec fn spec_dtor_calls(ls: Params, all: Fns, ps: Params, sd: Structs, line: u32) -> Result<DStmts, Refusal>
    decreases ls,
{
    match ls {
        List::Nil => Ok(List::Nil),
        List::Cons((v, t), rest) => match spec_dtor_call(v, t, all, ps, sd, line) {
            Err(r) => Err(r),
            Ok(d) => match spec_dtor_calls(*rest, all, ps, sd, line) {
                Err(r) => Err(r),
                Ok(ds) => Ok(List::Cons((Box::new(d), line), Box::new(ds))),
            },
        },
    }
}

pub fn dtor_calls(ls: &Params, all: &Fns, ps: &Params, sd: &Structs, line: u32) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_dtor_calls(*ls, *all, *ps, *sd, line),
    decreases ls,
{
    match ls {
        List::Nil => Ok(List::Nil),
        List::Cons((v, t), rest) => match dtor_call(*v, *t, all, ps, sd, line) {
            Err(r) => Err(r),
            Ok(d) => match dtor_calls(rest, all, ps, sd, line) {
                Err(r) => Err(r),
                Ok(ds) => Ok(List::Cons((Box::new(d), line), Box::new(ds))),
            },
        },
    }
}

/// The destructors that run at the end of a block, for the locals it declares, unless the block ends with a return or an exit.
pub open spec fn spec_block_end(ss: Stmts, all: Fns, ps: Params, sd: Structs) -> Result<Option<DStmt>, Refusal> {
    let ls = spec_live(spec_block_locals(ss, List::Nil), sd);
    if ls is Nil || spec_ends_out(ss) {
        Ok(None)
    } else {
        match spec_dtor_calls(ls, all, ps, sd, spec_last_place(ss)) {
            Err(r) => Err(r),
            Ok(ds) => Ok(Some(DStmt::Dtors(Box::new(ds)))),
        }
    }
}

pub fn block_end(ss: &Stmts, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<Option<DStmt>, Refusal>)
    ensures
        r == spec_block_end(*ss, *all, *ps, *sd),
{
    let ls = live(&block_locals(ss, List::Nil), sd);
    if matches!(ls, List::Nil) || ends_out(ss) {
        Ok(None)
    } else {
        match dtor_calls(&ls, all, ps, sd, last_place(ss)) {
            Err(r) => Err(r),
            Ok(ds) => Ok(Some(DStmt::Dtors(Box::new(ds)))),
        }
    }
}

/// An expression that copies a value of a struct with a destructor: a name of such a type, or a reference parameter of one.
pub open spec fn spec_dtor_copy(e: Expr, sd: Structs) -> bool
    decreases e,
{
    match e {
        Expr::Var(_, t) => spec_dtor_of(t, sd) is Some || match t {
            Ty::Mut(Scalar::Struct(k)) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            _ => false,
        },
        Expr::Cast(c, a) => (c == CastKind::Read || c == CastKind::NoOp) && spec_dtor_copy(*a, sd),
        Expr::Paren(a) => spec_dtor_copy(*a, sd),
        _ => false,
    }
}

pub fn dtor_copy(e: &Expr, sd: &Structs) -> (r: bool)
    ensures
        r == spec_dtor_copy(*e, *sd),
    decreases e,
{
    match e {
        Expr::Var(_, t) => dtor_of(*t, sd).is_some() || match t {
            Ty::Mut(Scalar::Struct(k)) => dtor_of(Ty::Struct(*k), sd).is_some(),
            _ => false,
        },
        Expr::Cast(c, a) => (*c == CastKind::Read || *c == CastKind::NoOp) && dtor_copy(a, sd),
        Expr::Paren(a) => dtor_copy(a, sd),
        _ => false,
    }
}

/// The callee gives a value of a struct with a destructor: a constructor of one, or a function that gives one.
pub open spec fn spec_callee_dtor(all: Fns, key: u32, sd: Structs) -> bool {
    match spec_find(all, key) {
        Some(f) => match f.ret {
            Ty::This(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            Ty::Struct(k) => spec_dtor_of(Ty::Struct(k), sd) is Some,
            _ => false,
        },
        None => false,
    }
}

pub fn callee_dtor(all: &Fns, key: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_callee_dtor(*all, key, *sd),
{
    match find(all, key) {
        Some(f) => match f.ret {
            Ty::This(k) => dtor_of(Ty::Struct(k), sd).is_some(),
            Ty::Struct(k) => dtor_of(Ty::Struct(k), sd).is_some(),
            _ => false,
        },
        None => false,
    }
}

/// The check of a local of a struct with a destructor: its start value is a call of a constructor of the struct, and the
/// destructor has a contract.
pub open spec fn spec_dtor_local(t: Ty, e: Expr, all: Fns, sd: Structs, line: u32) -> Option<Refusal> {
    match t {
        Ty::Struct(k) => match spec_dtor_of(t, sd) {
            None => None,
            Some(key) => if !(match e {
                Expr::Call(c, _, _, _) => match spec_find(all, c) {
                    Some(f) => f.ret == Ty::This(k),
                    None => false,
                },
                _ => false,
            }) {
                Some(Refusal::Copy(line))
            } else if match spec_find(all, key) {
                Some(f) => f.conds is Nil,
                None => true,
            } {
                Some(Refusal::NoDtorContract(line))
            } else {
                None
            },
        },
        _ => if spec_holds_dtor(t, sd) { Some(Refusal::Copy(line)) } else { None },
    }
}

pub fn dtor_local(t: Ty, e: &Expr, all: &Fns, sd: &Structs, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_dtor_local(t, *e, *all, *sd, line),
{
    match t {
        Ty::Struct(k) => match dtor_of(t, sd) {
            None => None,
            Some(key) => {
                let made = match e {
                    Expr::Call(c, _, _, _) => match find(all, *c) {
                        Some(f) => f.ret == Ty::This(k),
                        None => false,
                    },
                    _ => false,
                };
                if !made {
                    Some(Refusal::Copy(line))
                } else if match find(all, key) {
                    Some(f) => matches!(f.conds, List::Nil),
                    None => true,
                } {
                    Some(Refusal::NoDtorContract(line))
                } else {
                    None
                }
            },
        },
        _ => if holds_dtor(t, sd) { Some(Refusal::Copy(line)) } else { None },
    }
}

/// A return of a function with locals that have destructors: the value, then each destructor, newest first, then the exit.
pub open spec fn spec_dying_return(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    // A value that runs a call only sometimes sets the result in each branch, decision 0177.
    if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        match spec_lower(e, None, true, all, l, sd, 0) {
            Err(r) => Err(r),
            Ok((ss, _)) => match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
                Err(r) => Err(r),
                Ok(ds) => Ok(DStmt::Block(Box::new(spec_append(
                    ss,
                    List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))),
                )))),
            },
        }
    } else {
    match spec_lift(e, all, l, sd, 0, true) {
        Err(r) => Err(r),
        Ok((c, d, _)) => match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
            Err(r) => Err(r),
            Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons(
                (Box::new(spec_pre(c, DStmt::SetResult(d))), l),
                Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))),
            )))),
        },
    }
    }
}

pub fn dying_return(e: &Expr, l: u32, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dying_return(*e, l, *all, *env, *ps, *sd),
{
    if !matches!(e, Expr::Call(..)) && cond_calls(e, all, l, sd) {
        match lower(e, None, true, all, l, sd, 0) {
            Err(r) => Err(r),
            Ok((ss, _)) => match dtor_calls(&live(env, sd), all, ps, sd, l) {
                Err(r) => Err(r),
                Ok(ds) => Ok(DStmt::Block(Box::new(append(
                    ss,
                    List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))),
                )))),
            },
        }
    } else {
    match lift(e, all, l, sd, 0, true) {
        Err(r) => Err(r),
        Ok((c, d, _)) => match dtor_calls(&live(env, sd), all, ps, sd, l) {
            Err(r) => Err(r),
            Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons(
                (Box::new(pre(c, DStmt::SetResult(d))), l),
                Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))),
            )))),
        },
    }
    }
}

/// An exit of a function with locals that have destructors runs each destructor first.
pub open spec fn spec_dying_exit(l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match spec_dtor_calls(spec_live(env, sd), all, ps, sd, l) {
        Err(r) => Err(r),
        Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))))),
    }
}

pub fn dying_exit(l: u32, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_dying_exit(l, *all, *env, *ps, *sd),
{
    match dtor_calls(&live(env, sd), all, ps, sd, l) {
        Err(r) => Err(r),
        Ok(ds) => Ok(DStmt::Block(Box::new(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))))))),
    }
}

/// A call that stands alone names a key with a method.
pub proof fn lemma_call_stmt_resolves(key: u32, name: u32, args: Args, line: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_call_stmt(key, name, args, line, all, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_call_stmt(key, name, args, line, all, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 3);
    if spec_call_lift(key, name, args, line, all, line, sd).is_ok() {
        lemma_call_lift_resolves(key, name, args, line, all, line, sd);
    }
    if let List::Cons(_, rest) = args {
        if spec_call_lift(key, name, *rest, line, all, line, sd).is_ok() {
            lemma_call_lift_resolves(key, name, *rest, line, all, line, sd);
        }
    }
}

/// The calls of destructors name keys with methods.
pub proof fn lemma_dtor_calls_resolve(ls: Params, all: Fns, ps: Params, sd: Structs, line: u32)
    requires
        spec_dtor_calls(ls, all, ps, sd, line).is_ok(),
    ensures
        calls_resolve(spec_dtor_calls(ls, all, ps, sd, line).unwrap(), all, sd),
    decreases ls,
{
    match ls {
        List::Nil => {},
        List::Cons((v, t), rest) => {
            let key = spec_dtor_of(t, sd).unwrap();
            let f = spec_find(all, key).unwrap();
            lemma_call_stmt_resolves(key, DTOR_NAME, List::Cons(Box::new(Expr::Var(v, t)), Box::new(spec_dtor_globals(spec_tail(f.params), ps))), line, all, ps, sd);
            lemma_dtor_calls_resolve(*rest, all, ps, sd, line);
        },
    }
}

pub proof fn lemma_block_end_resolves(ss: Stmts, all: Fns, ps: Params, sd: Structs)
    requires
        spec_block_end(ss, all, ps, sd).is_ok(),
    ensures
        match spec_block_end(ss, all, ps, sd).unwrap() {
            Some(d) => calls_resolve(List::Cons((Box::new(d), spec_last_place(ss)), Box::new(List::Nil)), all, sd),
            None => true,
        },
{
    reveal_with_fuel(calls_resolve, 2);
    let ls = spec_live(spec_block_locals(ss, List::Nil), sd);
    if !(ls is Nil || spec_ends_out(ss)) {
        lemma_dtor_calls_resolve(ls, all, ps, sd, spec_last_place(ss));
    }
}

/// The start value of a local that is no vector: a call, or an expression whose calls run first, decision 0104.
pub open spec fn spec_local_value(n: u32, dt: DTy, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match e {
        Expr::Call(k, nm, args, at) => spec_local_call(n, dt, k, nm, *args, at, all, l, ps, sd),
        _ => match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, d))),
            Err(r) => Err(r),
        },
    }
}

pub fn local_value(n: u32, dt: DTy, e: &Expr, l: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_local_value(n, dt, *e, l, *all, *ps, *sd),
{
    match e {
        Expr::Call(k, nm, args, at) => local_call(n, dt, *k, *nm, args, *at, all, l, ps, sd),
        _ => match lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(pre(c, DStmt::Local(n, dt, d))),
            Err(r) => Err(r),
        },
    }
}

/// A `return`. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_return_stmt(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    // A return can move a local or a parameter, decision 0171. Nothing runs after it, so it sets nothing to null.
    match spec_move_check(spec_unmove(e).1, spec_var_names(e), ps, true, l) {
        Some(r) => Err(r),
        // A copy of a struct with a destructor has no rule, and the locals with destructors die after the value, decision 0178.
        None => if spec_dtor_copy(spec_unmove(e).0, sd) {
            Err(Refusal::Copy(l))
        } else if spec_live(env, sd) is Nil {
            spec_return(spec_unmove(e).0, l, all, ps, sd)
        } else {
            spec_dying_return(spec_unmove(e).0, l, all, env, ps, sd)
        },
    }
}

/// A local. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_local_stmt(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    match t {
        // A local vector is a copy of a sequence in scope of the same element, decision 0160, or the vector that a call gives,
        // decision 0163. A vector of a struct with a destructor is a copy, decision 0178.
        Ty::Vec(s) => if spec_holds_dtor(Ty::Vec(s), sd) { Err(Refusal::Copy(l)) } else { match spec_value_ty(Ty::Vec(s), l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => spec_local_call(n, dt, k, nm, *args, at, all, l, ps, sd),
                // The source is a name in scope, decision 0164.
                Expr::Copy(a, from, _) => if spec_seq_elem(from) == Some(s) && match *a {
                    Expr::Var(w, _) => spec_get(env, w) is Some || spec_get(ps, w) is Some,
                    _ => false,
                } {
                    match spec_lift(e, all, l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, d))),
                        Err(r) => Err(r),
                    }
                } else {
                    Err(Refusal::VecLocal(l))
                },
                // A local vector with no initial value is the empty sequence, decision 0170.
                Expr::EmptyVec => Ok(DStmt::Local(n, dt, DExpr::EmptySeq)),
                // `v(n, x)` is a vector of n copies of x, decision 0185. The count lifts first, then the value.
                Expr::Fill(c, x) => match spec_lift(*c, all, l, sd, 0, true) {
                    Err(r) => Err(r),
                    Ok((c1, dc, n1)) => match spec_lift(*x, all, l, sd, n1, true) {
                        Err(r) => Err(r),
                        Ok((c2, dx, _)) => Ok(spec_pre(spec_append(c1, c2), DStmt::Local(n, dt, DExpr::SeqFill(Box::new(dc), Box::new(dx))))),
                    },
                },
                // A move of a vector gives the local its value, and the source then has any value, decision 0185.
                Expr::Move(w, _) => match spec_get(ps, w) {
                    Some(Ty::MutSeq(s2)) => if s2 == s {
                        Ok(DStmt::Gone(Box::new(DStmt::Local(n, dt, DExpr::Out(w))), w, true))
                    } else {
                        Err(Refusal::VecLocal(l))
                    },
                    Some(_) => Err(Refusal::WriteParam(w, l)),
                    None => match spec_get(env, w) {
                        Some(Ty::Vec(s2)) => if s2 == s {
                            Ok(DStmt::Gone(Box::new(DStmt::Local(n, dt, DExpr::Var(w))), w, false))
                        } else {
                            Err(Refusal::VecLocal(l))
                        },
                        _ => Err(Refusal::VecLocal(l)),
                    },
                },
                _ => Err(Refusal::VecLocal(l)),
            },
        } },
        // A local std::array from a brace list of its length is the sequence of the values, decision 0184.
        Ty::Seq(_, Extent::Fixed(k)) => if spec_holds_dtor(t, sd) { Err(Refusal::Copy(l)) } else { match e {
            Expr::List(args) => if spec_count_args(*args) as u64 != k {
                Err(Refusal::BraceLen(spec_count_args(*args), spec_extent32(k), l))
            } else {
                match spec_ty(t, l) {
                    Err(r) => Err(r),
                    Ok(dt) => match spec_lift_args(*args, all, l, sd, 0, true) {
                        Ok((c, da, _)) => Ok(spec_pre(c, DStmt::Local(n, dt, DExpr::SeqLit(Box::new(da))))),
                        Err(r) => Err(r),
                    },
                }
            },
            _ => Err(Refusal::SeqParam(l)),
        } },
        // The start value of a local can move a local, decision 0171.
        _ => match spec_value_ty(t, l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match spec_dtor_local(t, e, all, sd, l) {
                Some(r) => Err(r),
                None => match spec_move_check(spec_unmove(e).1, spec_var_names(e), ps, false, l) {
                    Some(r) => Err(r),
                    None => match spec_local_value(n, dt, spec_unmove(e).0, l, all, ps, sd) {
                        Ok(d) => Ok(spec_moved(d, spec_unmove(e).1)),
                        Err(r) => Err(r),
                    },
                },
            },
        },
    }
}

/// An assignment. It is hidden, so a proof about another kind of statement does not unfold it.
#[verifier::opaque]
pub open spec fn spec_assign_stmt(n: u32, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs) -> Result<DStmt, Refusal> {
    if spec_is_mut(ps, n) {
        match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => Ok(spec_pre(c, DStmt::SetOut(n, d))),
            Err(r) => Err(r),
        }
    } else if (spec_get(ps, n) is Some) {
        Err(Refusal::WriteParam(n, l))
    } else {
        match e {
            // The value of a call that gives a struct with a destructor is a temporary, decision 0178.
            Expr::Call(k, nm, args, at) => if spec_callee_dtor(all, k, sd) {
                Err(Refusal::Copy(l))
            } else if spec_callee_writes(all, k) {
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
    }
}

/// A statement of the body, and a list of them. `env` is the variables in scope, and `ps` the parameters. A call runs before its
/// statement where C++ runs it once, decision 0104, and a call of a function that writes its object or gives no value stands
/// alone. A write is to a local, never to a parameter, or to a field of the object of a member function that writes it, decision
/// 0096.
// ponytail: `x = o.f();` of a function that writes its object is refused as a call out of place. Upgrade: an update to a fresh
// local, then the write. `return o.f();` writes back and returns, decision 0174.
pub open spec fn spec_stmt(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmt, Refusal>
    decreases s, 0nat,
{
    match s {
        Stmt::Return(e, l) => spec_return_stmt(e, l, all, env, ps, sd),
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
        Stmt::Local(n, t, e, l) => spec_local_stmt(n, t, e, l, all, env, ps, sd),
        Stmt::Assign(n, e, l) => spec_assign_stmt(n, e, l, all, ps, sd),
        // `++` and `--` on a double round, decision 0150.
        Stmt::Step(n, t, up, l) => if t == Ty::F64 {
            Err(Refusal::Rounds(l))
        } else if (spec_get(ps, n) is Some) && !spec_is_mut(ps, n) {
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
                Ok(dec) => match spec_loop_test(c, all, l, sd) {
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
                    Ok(di) => match spec_loop_test(c, all, l, sd) {
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
        // A write through a local unique_ptr writes the value that it owns. The value can move a local, and the statement reads
        // the pointer, so the pointer cannot move in it, decision 0186.
        Stmt::SetOwnField(n, f, e, l) => if spec_get(ps, n) is Some {
            Err(Refusal::WriteParam(n, l))
        } else {
            match spec_get(env, n) {
                Some(Ty::Own(Scalar::Struct(k))) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(l)),
                    Some(_) => match spec_move_check(spec_unmove(e).1, List::Cons(n, Box::new(spec_var_names(e))), ps, false, l) {
                        Some(r) => Err(r),
                        None => match spec_lift(spec_unmove(e).0, all, l, sd, 0, true) {
                            Ok((c, d, _)) => Ok(spec_moved(spec_pre(c, DStmt::SetOwnField(n, f, d)), spec_unmove(e).1)),
                            Err(r) => Err(r),
                        },
                    },
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::Syntax(l)),
            }
        },
        Stmt::Switch(e, k, cs, l) => match spec_lift(e, all, l, sd, 0, true) {
            Ok((c, d, _)) => match spec_cases(*cs, all, env, ps, sd) {
                Ok(dc) => Ok(spec_pre(c, DStmt::Match(d, k, Box::new(dc)))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        // A call that stands alone can move a local, decision 0171.
        Stmt::Call(k, nm, args, l) => match spec_move_check(spec_unmove_args(*args).1, spec_var_names_args(*args), ps, false, l) {
            Some(r) => Err(r),
            None => match spec_call_stmt(k, nm, spec_unmove_args(*args).0, l, all, ps, sd) {
                Ok(d) => Ok(spec_moved(d, spec_unmove_args(*args).1)),
                Err(r) => Err(r),
            },
        },
        Stmt::Exit(l) => if spec_live(env, sd) is Nil {
            Ok(DStmt::Exit)
        } else {
            spec_dying_exit(l, all, env, ps, sd)
        },
        Stmt::Block(b, _) => match spec_stmts(*b, all, env, ps, sd) {
            Ok(db) => Ok(DStmt::Scope(Box::new(db))),
            Err(r) => Err(r),
        },
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
            // A write to a local vector is a new value of the local, decision 0160, and so is a write to a local std::array,
            // decision 0184.
            None => match spec_get(env, v) {
                Some(Ty::Vec(_)) => match spec_code(i, l) {
                    Ok(di) => match spec_code(e, l) {
                        Ok(de) => Ok(DStmt::Assign(v, DExpr::SetAt(Box::new(DExpr::Var(v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                Some(Ty::Seq(_, Extent::Fixed(_))) => match spec_code(i, l) {
                    Ok(di) => match spec_code(e, l) {
                        Ok(de) => Ok(DStmt::Assign(v, DExpr::SetAt(Box::new(DExpr::Var(v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(l)),
            },
        },
        // `f[i] = e` of a sequence field in a member function that writes its object is a new value of the field, decision 0187.
        Stmt::SetFieldAt(f, i, e, l) => match spec_self(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match spec_field_ty(sd, k, f) {
                    Some(Ty::Seq(_, _)) => match spec_code(i, l) {
                        Ok(di) => match spec_code(e, l) {
                            Ok(de) => Ok(DStmt::SetField(f, DExpr::SetAt(Box::new(DExpr::Field(Box::new(DExpr::After), f)), Box::new(di), Box::new(de)))),
                            Err(r) => Err(r),
                        },
                        Err(r) => Err(r),
                    },
                    Some(_) => Err(Refusal::Syntax(l)),
                    None => Err(Refusal::NoField(f, l)),
                },
                _ => Err(Refusal::WriteParam(p, l)),
            },
            None => Err(Refusal::Syntax(l)),
        },
        // `v.push_back(e)` appends one element, decision 0148. A failed push_back throws and never returns to verified code.
        // ponytail: a call in the value is refused as out of place, as for SetIndex. Upgrade: lift the calls, decision 0104.
        // `v.push_back(std::make_unique<D>(a))` runs the constructor of `D` before it, decision 0170.
        Stmt::PushBack(v, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(_)) => match spec_push_value(e, all, l, sd) {
                Ok((c, de)) => Ok(spec_pre(c, DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(de))))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(_)) => match spec_push_value(e, all, l, sd) {
                    Ok((c, de)) => Ok(spec_pre(c, DStmt::Assign(v, DExpr::Append(Box::new(DExpr::Var(v)), Box::new(de))))),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(l)),
            },
        },
        // `std::sort(v.begin(), v.end())` of a vector of integers, decision 0161.
        Stmt::Sort(v, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(s)) => spec_sort(DExpr::Out(v), s, l),
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(s)) => spec_sort(DExpr::Var(v), s, l),
                _ => Err(Refusal::SortForm(l)),
            },
        },
        // `std::sort` with a comparator lambda, decision 0162.
        Stmt::SortBy(v, a, b, t, e, l) => match spec_get(ps, v) {
            Some(Ty::MutSeq(s)) => spec_sort_by(DExpr::Out(v), s, a, b, t, e, l),
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match spec_get(env, v) {
                Some(Ty::Vec(s)) => spec_sort_by(DExpr::Var(v), s, a, b, t, e, l),
                _ => Err(Refusal::SortForm(l)),
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(k, l)),
    }
}

/// The cases of a switch, each body over the variables in scope at the switch, decision 0109.
pub open spec fn spec_cases(cs: Cases, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DCases, Refusal>
    decreases cs, 0nat,
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

/// The statements of a block, then the destructors of the locals that the block declares, decision 0178.
pub open spec fn spec_stmts(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss, 1nat,
{
    match spec_stmts_seq(ss, all, env, ps, sd) {
        Err(r) => Err(r),
        Ok(ds) => spec_with_end(ds, spec_block_end(ss, all, ps, sd), spec_last_place(ss)),
    }
}

/// The statements `ds` of a block, then what runs at its end.
pub open spec fn spec_with_end(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32) -> Result<DStmts, Refusal> {
    match end {
        Err(r) => Err(r),
        Ok(None) => Ok(ds),
        Ok(Some(d)) => Ok(spec_append(ds, List::Cons((Box::new(d), place), Box::new(List::Nil)))),
    }
}

/// What runs at the end of a block is the destructors, which are no statement of C++.
pub proof fn lemma_block_end_dtors(ss: Stmts, all: Fns, ps: Params, sd: Structs)
    ensures
        spec_block_end(ss, all, ps, sd) matches Ok(Some(d)) ==> d is Dtors,
{
}

pub proof fn lemma_with_end_count(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32)
    requires
        end is Ok,
        end matches Ok(Some(d)) ==> d is Dtors,
    ensures
        count_dstmts(spec_with_end(ds, end, place).unwrap()) == count_dstmts(ds),
{
    if let Ok(Some(d)) = end {
        let tail: DStmts = List::Cons((Box::new(d), place), Box::new(List::Nil));
        lemma_count_append(ds, tail);
        assert(d is Dtors);
        assert(count_dstmt(d) == 0);
        reveal_with_fuel(count_dstmts, 2);
        assert(count_dstmts(tail) == 0);
    }
}

pub proof fn lemma_with_end_resolves(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32, all: Fns, sd: Structs)
    requires
        end is Ok,
        calls_resolve(ds, all, sd),
        end matches Ok(Some(d)) ==> calls_resolve(List::Cons((Box::new(d), place), Box::new(List::Nil)), all, sd),
    ensures
        calls_resolve(spec_with_end(ds, end, place).unwrap(), all, sd),
{
    if let Ok(Some(d)) = end {
        lemma_resolve_append(ds, List::Cons((Box::new(d), place), Box::new(List::Nil)), all, sd);
    }
}

pub open spec fn spec_stmts_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs) -> Result<DStmts, Refusal>
    decreases ss, 0nat,
{
    match ss {
        List::Nil => Ok(List::Nil),
        // The writes of each statement are checked first, decision 0177.
        List::Cons(s, rest) => match spec_write_check(*s, all, ps, sd) {
            Some(r) => Err(r),
            None => match spec_stmt(*s, all, env, ps, sd) {
                Ok(d) => match spec_stmts_seq(*rest, all, spec_scope(*s, env), ps, sd) {
                    Ok(dr) => Ok(List::Cons((Box::new(d), spec_place(*s)), Box::new(dr))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
        },
    }
}

/// An expression names `result`.
pub open spec fn spec_has_result(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Result => true,
        Expr::Finite(a) => spec_has_result(*a),
        Expr::Abs(a) => spec_has_result(*a),
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
            // The pass of decision 0173 consumes each reads line that names a global.
            CondKind::Reads => Err(Refusal::Construct(READS_NAME, l)),
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
        Stmt::Block(b, _) => spec_twice_stmts(seen, *b),
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

/// The names that a body moves outside a `return`, at any depth, in their order, decision 0186. A move stands only at the start
/// value of a local, in a call that stands alone and in a write through a unique_ptr, so these are the only places to look.
pub open spec fn spec_moves_stmts(ss: Stmts) -> Names
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_moves_stmt(*s), spec_moves_stmts(*rest)),
    }
}

pub open spec fn spec_moves_stmt(s: Stmt) -> Names
    decreases s,
{
    match s {
        Stmt::Local(_, _, e, _) => spec_unmove(e).1,
        Stmt::Call(_, _, args, _) => spec_unmove_args(*args).1,
        Stmt::SetOwnField(_, _, e, _) => spec_unmove(e).1,
        Stmt::If(_, t, f, _) => spec_append(spec_moves_stmts(*t), spec_moves_stmts(*f)),
        Stmt::While(_, _, body, _) => spec_moves_stmts(*body),
        Stmt::For(init, _, step, _, body, _) => spec_append(spec_moves_stmt(*init), spec_append(spec_moves_stmt(*step), spec_moves_stmts(*body))),
        Stmt::Switch(_, _, cs, _) => spec_moves_cases(*cs),
        Stmt::RangeFor(_, _, _, _, _, body, _) => spec_moves_stmts(*body),
        Stmt::Block(b, _) => spec_moves_stmts(*b),
        _ => List::Nil,
    }
}

pub open spec fn spec_moves_cases(cs: Cases) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_moves_stmts(*body), spec_moves_cases(*rest)),
    }
}

/// The unique_ptr parameters among `ps` that the body moves, by their names and what they own, decision 0186.
pub open spec fn spec_moved_params(ps: Params, ms: Names) -> List<(u32, Scalar)>
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Own(s) => if spec_has(ms, n) {
                List::Cons((n, s), Box::new(spec_moved_params(*rest, ms)))
            } else {
                spec_moved_params(*rest, ms)
            },
            _ => spec_moved_params(*rest, ms),
        },
    }
}

/// The parameters among `ps` that stay parameters of the body: each one but a unique_ptr that the body moves, decision 0186.
pub open spec fn spec_kept_params(ps: Params, ms: Names) -> Params
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if (t is Own) && spec_has(ms, n) {
            spec_kept_params(*rest, ms)
        } else {
            List::Cons((n, t), Box::new(spec_kept_params(*rest, ms)))
        },
    }
}

/// `var p: Option<T> := p;` for each moved parameter, at the line of the function, then `tail`, decision 0186.
pub open spec fn spec_param_locals(mp: List<(u32, Scalar)>, line: u32, tail: DStmts) -> DStmts
    decreases mp,
{
    match mp {
        List::Nil => tail,
        List::Cons((n, s), rest) => List::Cons((Box::new(DStmt::Local(n, DTy::Opt(s), DExpr::Var(n))), line), Box::new(spec_param_locals(*rest, line, tail))),
    }
}

/// The body with a local for each moved parameter. The body is a block, so Dafny reads each name in it as the local, and a contract
/// reads the parameter. A body that moves no parameter stays as it is, decision 0186.
pub open spec fn spec_param_block(mp: List<(u32, Scalar)>, line: u32, body: DStmts) -> DStmts {
    match mp {
        List::Nil => body,
        _ => List::Cons((Box::new(DStmt::Scope(Box::new(spec_param_locals(mp, line, body)))), line), Box::new(List::Nil)),
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
                        // A unique_ptr parameter that the body moves is a local of the body, decision 0186.
                        None => match spec_stmts(f.body, all, f.params, spec_kept_params(f.params, spec_moves_stmts(f.body)), sd) {
                            Err(r) => Err(r),
                            Ok(body) => Ok((req, ens, dec, spec_param_block(spec_moved_params(f.params, spec_moves_stmts(f.body)), f.line, body))),
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
/// The value of a body of apply lines and one return: the value of the return after each lemma, in order, decision 0167. A local
/// before the return is a `var` of the value, decision 0172. A call of a const virtual function of an interface as the value of the
/// return or of a local is the function of the interface, whose method gives the same value, decision 0166.
pub open spec fn spec_pure_value(body: DStmts, all: Fns) -> Option<DExpr>
    decreases body,
{
    match body {
        List::Cons((s, _), rest) => match *s {
            DStmt::Return(d) => if *rest == List::Nil {
                Some(d)
            } else {
                None
            },
            DStmt::ReturnCall(k, da) => if *rest == List::Nil && spec_inline(all, k) {
                Some(DExpr::FCall(k, Box::new(da)))
            } else {
                None
            },
            DStmt::Apply(f, da) => match spec_pure_value(*rest, all) {
                Some(e) => Some(DExpr::Lemma(f, Box::new(da), Box::new(e))),
                None => None,
            },
            DStmt::Local(n, dt, d) => match spec_pure_value(*rest, all) {
                Some(e) => Some(DExpr::Let(n, dt, Box::new(d), Box::new(e))),
                None => None,
            },
            DStmt::LocalCall(n, dt, k, da) => if spec_inline(all, k) {
                match spec_pure_value(*rest, all) {
                    Some(e) => Some(DExpr::Let(n, dt, Box::new(DExpr::FCall(k, Box::new(da))), Box::new(e))),
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        },
        List::Nil => None,
    }
}

/// A member function with `this`, or a static member function, `stat`, that writes nothing, has the value of its pure body as its
/// function, decisions 0090 and 0174. A free function never has one.
pub open spec fn spec_pure_body(ps: Params, body: DStmts, all: Fns, stat: bool) -> Option<DExpr> {
    if (spec_this(ps) is Some || stat) && !spec_mutates(ps) {
        spec_pure_value(body, all)
    } else {
        None
    }
}

/// The function with the key `k` is a member of a struct of the file and has no object, so it is a static member function,
/// decision 0174.
pub open spec fn spec_static_key(sd: Structs, k: u32) -> bool
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => spec_member_key(ms, k) || spec_static_key(*rest, k),
    }
}

pub open spec fn spec_member_key(ms: Members, k: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (key, _)), rest) => key == k || spec_member_key(*rest, k),
    }
}

pub fn static_key(sd: &Structs, k: u32) -> (r: bool)
    ensures
        r == spec_static_key(*sd, k),
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => member_key(ms, k) || static_key(rest, k),
    }
}

pub fn member_key(ms: &Members, k: u32) -> (r: bool)
    ensures
        r == spec_member_key(*ms, k),
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (key, _)), rest) => *key == k || member_key(rest, k),
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
        Some(_) => spec_link(f, ens),
        None => if spec_const_virtual(f) {
            // The method of a virtual function gives the value of its function, decision 0166.
            spec_link(f, ens)
        } else {
            ens
        },
    }
}

/// The interface of a virtual function: its first parameter is `this` of it, decision 0165.
pub open spec fn spec_virtual(f: Function) -> Option<u32> {
    match spec_head_ty(f.params) {
        Some(Ty::Iface(k)) => Some(k),
        Some(Ty::IfaceMut(k)) => Some(k),
        _ => None,
    }
}

/// A virtual function that does not write its object: a function of the model, decision 0166.
pub open spec fn spec_const_virtual(f: Function) -> bool {
    spec_head_ty(f.params) is Some && spec_head_ty(f.params)->Some_0 is Iface
}

/// Each member marked as no function in the model.
pub open spec fn spec_unmark(ms: Members) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, _)), rest) => List::Cons((n, (k, None)), Box::new(spec_unmark(*rest))),
    }
}

/// The members, with the member of the function `key` and each one after it marked as no function in the model.
pub open spec fn spec_from(ms: Members, key: u32) -> Members
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, p)), rest) => if k == key {
            spec_unmark(ms)
        } else {
            List::Cons((n, (k, p)), Box::new(spec_from(*rest, key)))
        },
    }
}

/// The table that a contract of the virtual function `key` of the interface `b` reads: only the functions above it in `b` are
/// functions of the model, decision 0166.
pub open spec fn spec_above(sd: Structs, b: u32, key: u32) -> Structs
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => if k == b {
            List::Cons((k, (l, fields, spec_from(ms, key))), Box::new(spec_above(*rest, b, key)))
        } else {
            List::Cons((k, (l, fields, ms)), Box::new(spec_above(*rest, b, key)))
        },
    }
}

/// The table that the contract of `f` reads. A virtual function has no body, so the table reads only its contract.
pub open spec fn spec_view_of(f: Function, sd: Structs) -> Structs {
    match spec_virtual(f) {
        Some(b) => if f.trusted {
            spec_above(sd, b, f.name)
        } else {
            sd
        },
        None => sd,
    }
}

/// The name of the member of the function `key`.
pub open spec fn spec_member_name(ms: Members, key: u32) -> Option<u32>
    decreases ms,
{
    match ms {
        List::Nil => None,
        List::Cons((n, (k, _)), rest) => if k == key {
            Some(n)
        } else {
            spec_member_name(*rest, key)
        },
    }
}

/// The first member of the name `g` is the member of the function `key` or comes after it.
pub open spec fn spec_at_or_after(ms: Members, key: u32, g: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((n, (k, _)), rest) => if k == key {
            spec_get(ms, g) is Some
        } else if n == g {
            false
        } else {
            spec_at_or_after(*rest, key, g)
        },
    }
}

/// Each member of `ms` from the one of the function `key` on is no function in the model of `spec_from`.
pub proof fn lemma_from_unmarks(ms: Members, key: u32, g: u32)
    requires
        spec_at_or_after(ms, key, g),
    ensures
        match spec_get(spec_from(ms, key), g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((_, (k, _)), rest) => if k == key {
            lemma_unmark_none(ms, g);
        } else {
            lemma_from_unmarks(*rest, key, g);
        },
    }
}

proof fn lemma_unmark_none(ms: Members, g: u32)
    requires
        spec_get(ms, g) is Some,
    ensures
        match spec_get(spec_unmark(ms), g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((n, _), rest) => if n != g {
            lemma_unmark_none(*rest, g);
        },
    }
}

/// A contract of a virtual function reads no function of its interface at or after it as a function of the model, decision 0166.
/// So the functions of the model of an interface call each other in the order of the interface, with no cycle.
pub proof fn lemma_a_later_function_is_no_function(sd: Structs, b: u32, key: u32, g: u32)
    requires
        match spec_get(sd, b) {
            Some((_, _, ms)) => spec_at_or_after(ms, key, g),
            None => false,
        },
    ensures
        match spec_member(spec_above(sd, b, key), b, g) {
            Some((_, p)) => p is None,
            None => false,
        },
    decreases sd,
{
    match sd {
        List::Nil => {},
        List::Cons((k, (_, _, ms)), rest) => if k == b {
            lemma_from_unmarks(ms, key, g);
        } else {
            lemma_a_later_function_is_no_function(*rest, b, key, g);
        },
    }
}

/// The refusal of a contract of `f`. A virtual function that reads a later function of its interface gets `Later`, decision 0166.
pub open spec fn spec_late(f: Function, sd: Structs, r: Refusal) -> Refusal {
    match spec_virtual(f) {
        Some(b) => match r {
            Refusal::NotPure(g, l) => match spec_get(sd, b) {
                Some((_, _, ms)) => if spec_at_or_after(ms, f.name, g) {
                    match spec_member_name(ms, f.name) {
                        Some(n) => Refusal::Later(b, n, g, l),
                        None => r,
                    }
                } else {
                    r
                },
                None => r,
            },
            _ => r,
        },
        None => r,
    }
}

/// The contract and the body of `f` under the table that its contract reads, decision 0166.
pub open spec fn spec_inside_of(f: Function, all: Fns, sd: Structs) -> Result<(DConds, DConds, DConds, DStmts), Refusal> {
    match spec_inside(f, all, spec_view_of(f, sd)) {
        Ok(x) => Ok(x),
        Err(r) => Err(spec_late(f, sd, r)),
    }
}

/// The ensures lines of a method with one more: `result == F(params)`, at the line of the function.
pub open spec fn spec_link(f: Function, ens: DConds) -> DConds {
    spec_append(
        ens,
        List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(spec_param_args(f.params))))), f.line), Box::new(List::Nil)),
    )
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
        // An interface has no field, and its member functions are its virtual functions, decision 0166.
        Ty::Iface(k) => Some(k),
        Ty::IfaceRef(k) => Some(k),
        Ty::IfaceMut(k) => Some(k),
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
        Some(f) => if !has_signature(f, sd) {
            None
        } else if spec_const_virtual(f) {
            // A virtual function is a function of the model with no body, decision 0166.
            if !strict {
                Some((f.ret, f.params))
            } else {
                match spec_inside_of(f, all, sd) {
                    Ok(_) => Some((f.ret, f.params)),
                    Err(_) => None,
                }
            }
        } else if f.trusted {
            None
        } else if strict {
            match spec_inside(f, all, sd) {
                Ok((_, _, _, body)) => match spec_pure_body(f.params, body, all, spec_static_key(sd, f.name)) {
                    Some(_) => Some((f.ret, f.params)),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match spec_stmts(f.body, all, f.params, f.params, sd) {
                Ok(body) => match spec_pure_body(f.params, body, all, spec_static_key(sd, f.name)) {
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

// ------------------------------------------------------------------ virtual functions, decision 0165

/// The check of one override. `base` and `derived` are the keys of the function of the interface and of the override. `params` are
/// the parameters of the override after `this`. `requires` and `ensures` are the contract of the function of the interface, read on
/// the parameters of the override. `own` is the requires lines of the override. Dafny proves that `own` follows from `requires`, and
/// that the function of the override meets `ensures`. `promise` is the ensures lines of the override. An override that writes has
/// no function, so Dafny proves that `promise` gives `ensures`, decision 0169.
#[derive(PartialEq, Eq, Debug)]
pub struct DOverride {
    pub base: u32,
    pub derived: u32,
    pub params: DParams,
    pub ret: DTy,
    pub requires: DConds,
    pub ensures: DConds,
    pub own: DConds,
    pub promise: DConds,
}

pub type DOverrides = List<DOverride>;

/// The upcast from the final class `derived` to the interface `base`, with the check of each override.
#[derive(PartialEq, Eq, Debug)]
pub struct DUpcast {
    pub derived: u32,
    pub base: u32,
    pub overrides: DOverrides,
}

/// The parameters have the same types in their order, whatever their names.
pub open spec fn spec_same_tys(a: Params, b: Params) -> bool
    decreases a,
{
    match a {
        List::Nil => b == List::<(u32, Ty)>::Nil,
        List::Cons((_, ta), ra) => match b {
            List::Cons((_, tb), rb) => ta == tb && spec_same_tys(*ra, *rb),
            List::Nil => false,
        },
    }
}

/// The type of the first parameter, `this` of a member function.
pub open spec fn spec_head_ty(ps: Params) -> Option<Ty> {
    match ps {
        List::Cons((_, t), _) => Some(t),
        List::Nil => None,
    }
}

/// The function `fb` of the interface `b` and the function `fd` of the class `d` have the same parameters after `this` and the
/// same result.
pub open spec fn spec_overrides_fn(fb: Function, fd: Function, d: u32, b: u32) -> bool {
    ((spec_head_ty(fb.params) == Some(Ty::Iface(b)) && spec_head_ty(fd.params) == Some(Ty::This(d))) || (spec_head_ty(fb.params) == Some(
        Ty::IfaceMut(b),
    ) && spec_head_ty(fd.params) == Some(Ty::ThisMut(d)))) && fb.ret == fd.ret && spec_same_tys(spec_tail(fb.params), spec_tail(fd.params))
}

/// The check of the function `fb` of the interface on its override `fd`. The contract of `fb` reads the parameters of `fd` by their
/// place, decision 0060.
pub open spec fn spec_check(fb: Function, fd: Function, sd: Structs) -> Result<DOverride, Refusal> {
    match spec_params(spec_tail(fd.params), fd.line, sd) {
        Err(r) => Err(r),
        Ok(ps) => match spec_ret_ty(fd.ret, fd.line, sd) {
            Err(r) => Err(r),
            Ok(ret) => match spec_conds(fb.conds, CondKind::Requires, fd.params, fd.ret, sd) {
                Err(r) => Err(r),
                Ok(rq) => match spec_conds(fb.conds, CondKind::Ensures, fd.params, fd.ret, sd) {
                    Err(r) => Err(r),
                    Ok(en) => match spec_conds(fd.conds, CondKind::Requires, fd.params, fd.ret, sd) {
                        Err(r) => Err(r),
                        Ok(own) => match spec_conds(fd.conds, CondKind::Ensures, fd.params, fd.ret, sd) {
                            Err(r) => Err(r),
                            Ok(promise) => Ok(DOverride { base: fb.name, derived: fd.name, params: ps, ret, requires: rq, ensures: en, own, promise }),
                        },
                    },
                },
            },
        },
    }
}

/// The check of the override in the class `d` of the virtual function `n` of the interface `b`, whose function has the key `bk`.
/// `line` is the line of `d`. The override must have the same parameters and result, and a function in the model, decision 0090.
pub open spec fn spec_override(d: u32, b: u32, n: u32, bk: u32, line: u32, all: Fns, sd: Structs) -> Result<DOverride, Refusal> {
    match spec_member(sd, d, n) {
        None => Err(Refusal::NoOverride(d, b, n, line)),
        Some((dk, pure)) => match spec_find(all, bk) {
            None => Err(Refusal::NoOverride(d, b, n, line)),
            Some(fb) => match spec_find(all, dk) {
                None => Err(Refusal::NoOverride(d, b, n, line)),
                Some(fd) => if !spec_overrides_fn(fb, fd, d, b) {
                    Err(Refusal::NoOverride(d, b, n, line))
                } else if spec_const_virtual(fb) && pure is None {
                    Err(Refusal::Unchecked(d, b, n, line))
                } else if !spec_const_virtual(fb) && !(spec_function(fd, all, sd) is Full) {
                    // An override that writes is checked on its contract, so it must have a method, decision 0169.
                    Err(Refusal::NoMethod(d, b, n, line))
                } else {
                    // The contract of the interface must have a model of its own, decision 0166.
                    match spec_inside_of(fb, all, sd) {
                        Err(r) => Err(r),
                        Ok(_) => spec_check(fb, fd, sd),
                    }
                },
            },
        },
    }
}

/// The checks of the overrides in `d` of the members `ms` of the interface `b`, or the first refusal.
pub open spec fn spec_override_each(d: u32, b: u32, ms: Members, line: u32, all: Fns, sd: Structs) -> Result<DOverrides, Refusal>
    decreases ms,
{
    match ms {
        List::Nil => Ok(List::Nil),
        List::Cons((n, (bk, _)), rest) => match spec_override(d, b, n, bk, line, all, sd) {
            Err(r) => Err(r),
            Ok(o) => match spec_override_each(d, b, *rest, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(List::Cons(o, Box::new(os))),
            },
        },
    }
}

/// The function that `spec_find` gives has the key it was asked for.
pub proof fn lemma_find_has_the_key(fs: Fns, key: u32)
    ensures
        match spec_find(fs, key) {
            Some(f) => f.name == key,
            None => true,
        },
    decreases fs,
{
    match fs {
        List::Nil => {},
        List::Cons(f, rest) => if f.name != key {
            lemma_find_has_the_key(*rest, key);
        },
    }
}

/// The checks `os` are one for each member of the interface `b` in `ms`, in their order. Each is of the member of `d` with the same
/// name, which has a function in the model and the same parameters and result.
pub open spec fn spec_checked(d: u32, b: u32, ms: Members, os: DOverrides, all: Fns, sd: Structs) -> bool
    decreases ms,
{
    match ms {
        List::Nil => os == List::<DOverride>::Nil,
        List::Cons((n, (bk, _)), rest) => match os {
            List::Nil => false,
            List::Cons(o, orest) => o.base == bk && match spec_member(sd, d, n) {
                Some((dk, p)) => o.derived == dk && match spec_find(all, bk) {
                    Some(fb) => match spec_find(all, dk) {
                        // A const override has a function in the model, and one that writes has a method, decision 0169.
                        Some(fd) => spec_overrides_fn(fb, fd, d, b) && (if spec_const_virtual(fb) {
                            p is Some
                        } else {
                            spec_function(fd, all, sd) is Full
                        }),
                        None => false,
                    },
                    None => false,
                },
                _ => false,
            } && spec_checked(d, b, *rest, *orest, all, sd),
        },
    }
}

/// The checks of the members of an interface are one for each member, in their order, each of an override with the same signature
/// and a function in the model.
pub proof fn lemma_each_member_is_checked(d: u32, b: u32, ms: Members, line: u32, all: Fns, sd: Structs)
    ensures
        match spec_override_each(d, b, ms, line, all, sd) {
            Ok(os) => spec_checked(d, b, ms, os, all, sd),
            Err(_) => true,
        },
    decreases ms,
{
    match ms {
        List::Nil => {},
        List::Cons((n, (bk, _)), rest) => {
            lemma_find_has_the_key(all, bk);
            match spec_member(sd, d, n) {
                Some((dk, _)) => lemma_find_has_the_key(all, dk),
                None => {},
            }
            lemma_each_member_is_checked(d, b, *rest, line, all, sd);
        },
    }
}

/// A member of the table has the function `key`.
pub open spec fn spec_keyed(ms: Members, key: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (k, _)), rest) => k == key || spec_keyed(*rest, key),
    }
}

/// Each function of `fs` whose first parameter is `this` of the interface `b` is in its member table `ms`. The plugin leaves out
/// a name that two functions share, decision 0090. A free function of `const B&` has `IfaceRef`, so it is none of them.
pub open spec fn spec_listed(fs: Fns, b: u32, ms: Members) -> bool
    decreases fs,
{
    match fs {
        List::Nil => true,
        List::Cons(f, rest) => (spec_virtual(*f) != Some(b) || spec_keyed(ms, f.name)) && spec_listed(*rest, b, ms),
    }
}

/// The upcast from the final class `d`, at the line `line`, to the interface `b`. The shell sends the interface from its table.
pub open spec fn spec_upcast(d: u32, b: u32, line: u32, all: Fns, sd: Structs) -> Result<DUpcast, Refusal> {
    match spec_get(sd, b) {
        None => Err(Refusal::Syntax(line)),
        Some((bl, _, ms)) => if !spec_listed(all, b, ms) {
            Err(Refusal::Overload(b, bl))
        } else {
            match spec_override_each(d, b, ms, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(DUpcast { derived: d, base: b, overrides: os }),
            }
        },
    }
}

/// An upcast holds only with a check of each virtual function of the interface. Each function with `this` of the interface is in
/// its member table, and each member has its check. A class with a virtual function with no override, or with an override that has
/// another signature or no function in the model, and an interface with two virtual functions of one name, have no upcast, decision
/// 0165.
pub proof fn lemma_each_virtual_function_is_checked(d: u32, b: u32, line: u32, all: Fns, sd: Structs)
    ensures
        match spec_upcast(d, b, line, all, sd) {
            Ok(up) => match spec_get(sd, b) {
                Some((_, _, ms)) => spec_listed(all, b, ms) && spec_checked(d, b, ms, up.overrides, all, sd),
                None => false,
            },
            Err(_) => true,
        },
{
    match spec_get(sd, b) {
        Some((_, _, ms)) => lemma_each_member_is_checked(d, b, ms, line, all, sd),
        None => {},
    }
}

/// The upcasts from the final class `d` to each of its interfaces `bs`, in their order.
pub open spec fn spec_upcasts_of(d: u32, bs: Names, line: u32, all: Fns, sd: Structs) -> List<Result<DUpcast, Refusal>>
    decreases bs,
{
    match bs {
        List::Nil => List::Nil,
        List::Cons(b, rest) => List::Cons(spec_upcast(d, b, line, all, sd), Box::new(spec_upcasts_of(d, *rest, line, all, sd))),
    }
}

/// The upcasts of each class over interfaces, by its key, the keys of its interfaces and whether it is final, in their order. A
/// class that is not final has none, and its refusal. The shell sends each class from its table.
pub open spec fn spec_upcasts(bases: List<(u32, (Names, bool))>, all: Fns, sd: Structs) -> List<Result<DUpcast, Refusal>>
    decreases bases,
{
    match bases {
        List::Nil => List::Nil,
        List::Cons((d, (bs, fin)), rest) => match spec_get(sd, d) {
            None => List::Cons(Err(Refusal::Syntax(0)), Box::new(spec_upcasts(*rest, all, sd))),
            Some((line, _, _)) => if !fin {
                List::Cons(Err(Refusal::NotFinal(d, line)), Box::new(spec_upcasts(*rest, all, sd)))
            } else {
                spec_append(spec_upcasts_of(d, bs, line, all, sd), spec_upcasts(*rest, all, sd))
            },
        },
    }
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
            Ok(ret) => match spec_checks(f) {
                Some(r) => Model::Refused(r),
                None => match spec_braces(f.body, spec_fixed(f.ret)) {
                Some(r) => Model::Bare(f.name, ps, ret, r),
                None => match spec_inside_of(f, all, sd) {
                    Err(r) => Model::Bare(f.name, ps, ret, r),
                    Ok((req, ens, dec, body)) => Model::Full(
                        Method {
                            name: f.name,
                            params: ps,
                            ret,
                            requires: spec_bounds(f.params, f.line, req),
                            ensures: spec_ret_len(f.ret, f.line, spec_linked(f, ens, spec_pure_body(f.params, body, all, spec_static_key(sd, f.name)))),
                            decreases: dec,
                            body,
                            function: spec_pure_body(f.params, body, all, spec_static_key(sd, f.name)),
                            writes: spec_writes(f.params),
                            outs: spec_outs(f.params),
                            trusted: f.trusted,
                        },
                    ),
                },
                },
            },
        },
    }
}

/// The checks of a signature with its contract: the modifies lines, decision 0108, and the words that keep NaN out, decision 0150.
pub open spec fn spec_checks(f: Function) -> Option<Refusal> {
    // A line that the translator cannot read gets its own refusal first, decision 0155. The pass of decision 0173 puts its
    // refusal on such a line.
    if spec_any_bad(f.conds) {
        None
    } else {
        match spec_modifies(f.params, f.conds, f.line) {
            Some(r) => Some(r),
            None => spec_finite(f.params, f.conds, f.trusted, f.ret, f.line),
        }
    }
}

/// The model holds no NaN and no infinity. So each double parameter needs `std::isfinite` of it in a requires line, and a trusted
/// function that gives a double needs `std::isfinite(result)` in an ensures line, decision 0150.
pub open spec fn spec_finite(ps: Params, cs: Conds, trusted: bool, ret: Ty, line: u32) -> Option<Refusal> {
    // A line that the translator cannot read gets its own refusal first, decision 0155.
    if spec_any_bad(cs) {
        None
    } else {
    match spec_unfinite(ps, ps, cs) {
        Some(p) => Some(Refusal::Finite(p, line)),
        None => if trusted && ret == Ty::F64 && !spec_finite_result(cs) {
            Some(Refusal::FiniteResult(line))
        } else {
            None
        },
    }
    }
}

/// A contract line that the shell could not cut or parse.
pub open spec fn spec_any_bad(cs: Conds) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _, _), rest) => k is Bad || spec_any_bad(*rest),
    }
}

pub fn any_bad(cs: &Conds) -> (r: bool)
    ensures
        r == spec_any_bad(*cs),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, _, _, _), rest) => (match k {
            CondKind::Bad(_) => true,
            _ => false,
        }) || any_bad(rest),
    }
}

/// The first double parameter among `todo` that no requires line says is finite.
pub open spec fn spec_unfinite(todo: Params, ps: Params, cs: Conds) -> Option<u32>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => if t == Ty::F64 && !spec_finite_said(ps, cs, p) {
            Some(p)
        } else {
            spec_unfinite(*rest, ps, cs)
        },
    }
}

/// A requires line says that the parameter `p` is finite.
pub open spec fn spec_finite_said(ps: Params, cs: Conds, p: u32) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => (k == CondKind::Requires && spec_says_finite(e, decl, ps, p)) || spec_finite_said(ps, *rest, p),
    }
}

/// `std::isfinite(x)` of the parameter `p`, alone or as a part joined by `&&`.
pub open spec fn spec_says_finite(e: Expr, decl: Names, ps: Params, p: u32) -> bool
    decreases e,
{
    match e {
        Expr::Finite(a) => match *a {
            Expr::Name(n) => match spec_rebind(decl, ps, n) {
                Some((q, _)) => q == p,
                None => false,
            },
            _ => false,
        },
        Expr::Bin(op, a, b) => op == BinOp::And && (spec_says_finite(*a, decl, ps, p) || spec_says_finite(*b, decl, ps, p)),
        Expr::Paren(a) => spec_says_finite(*a, decl, ps, p),
        _ => false,
    }
}

/// An ensures line says that the result is finite.
pub open spec fn spec_finite_result(cs: Conds) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, _), rest) => (k == CondKind::Ensures && spec_says_result_finite(e)) || spec_finite_result(*rest),
    }
}

/// `std::isfinite(result)`, alone or as a part joined by `&&`.
pub open spec fn spec_says_result_finite(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Finite(a) => *a is Result,
        Expr::Bin(op, a, b) => op == BinOp::And && (spec_says_result_finite(*a) || spec_says_result_finite(*b)),
        Expr::Paren(a) => spec_says_result_finite(*a),
        _ => false,
    }
}

pub fn checks(f: &Function) -> (r: Option<Refusal>)
    ensures
        r == spec_checks(*f),
{
    if any_bad(&f.conds) {
        None
    } else {
        match modifies(&f.params, &f.conds, f.line) {
            Some(r) => Some(r),
            None => finite(&f.params, &f.conds, f.trusted, f.ret, f.line),
        }
    }
}

pub fn finite(ps: &Params, cs: &Conds, trusted: bool, ret: Ty, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_finite(*ps, *cs, trusted, ret, line),
{
    if any_bad(cs) {
        return None;
    }
    match unfinite(ps, ps, cs) {
        Some(p) => Some(Refusal::Finite(p, line)),
        None => if trusted && ret == Ty::F64 && !finite_result(cs) {
            Some(Refusal::FiniteResult(line))
        } else {
            None
        },
    }
}

pub fn unfinite(todo: &Params, ps: &Params, cs: &Conds) -> (r: Option<u32>)
    ensures
        r == spec_unfinite(*todo, *ps, *cs),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((p, t), rest) => if *t == Ty::F64 && !finite_said(ps, cs, *p) {
            Some(*p)
        } else {
            unfinite(rest, ps, cs)
        },
    }
}

pub fn finite_said(ps: &Params, cs: &Conds, p: u32) -> (r: bool)
    ensures
        r == spec_finite_said(*ps, *cs, p),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, decl), rest) => (*k == CondKind::Requires && says_finite(e, decl, ps, p)) || finite_said(ps, rest, p),
    }
}

pub fn says_finite(e: &Expr, decl: &Names, ps: &Params, p: u32) -> (r: bool)
    ensures
        r == spec_says_finite(*e, *decl, *ps, p),
    decreases e,
{
    match e {
        Expr::Finite(a) => match &**a {
            Expr::Name(n) => match rebind(decl, ps, *n) {
                Some((q, _)) => q == p,
                None => false,
            },
            _ => false,
        },
        Expr::Bin(op, a, b) => *op == BinOp::And && (says_finite(a, decl, ps, p) || says_finite(b, decl, ps, p)),
        Expr::Paren(a) => says_finite(a, decl, ps, p),
        _ => false,
    }
}

pub fn finite_result(cs: &Conds) -> (r: bool)
    ensures
        r == spec_finite_result(*cs),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k, e, _, _), rest) => (*k == CondKind::Ensures && says_result_finite(e)) || finite_result(rest),
    }
}

pub fn says_result_finite(e: &Expr) -> (r: bool)
    ensures
        r == spec_says_result_finite(*e),
    decreases e,
{
    match e {
        Expr::Finite(a) => match &**a {
            Expr::Result => true,
            _ => false,
        },
        Expr::Bin(op, a, b) => *op == BinOp::And && (says_result_finite(a) || says_result_finite(b)),
        Expr::Paren(a) => says_result_finite(a),
        _ => false,
    }
}

/// The model of a struct: each field a type of the subset, decision 0073. A field can be a sequence, decision 0076.
pub open spec fn spec_fields(ps: Params, line: u32) -> Result<DParams, Refusal>
    decreases ps,
{
    match ps {
        List::Nil => Ok(List::Nil),
        // An optional of a struct is no field yet, decision 0137. A unique_ptr of a struct or an interface is a field, decision 0171.
        List::Cons((n, t), rest) => match (if (t is Opt && t->Opt_0 is Struct) || t is Ptr || (t is Own && !(t->Own_0 is Struct)) || t is F64 { Err(Refusal::Element(line)) } else { spec_ty(t, line) }) {
            Ok(dt) => match spec_fields(*rest, line) {
                Ok(dr) => Ok(List::Cons((n, dt), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
    }
}

pub open spec fn spec_structs(sd: Structs) -> StructModels {
    spec_structs_in(sd, sd)
}

/// A field that holds a struct with a destructor.
pub open spec fn spec_dtor_field(fields: Params, sd: Structs) -> bool
    decreases fields,
{
    match fields {
        List::Nil => false,
        List::Cons((_, t), rest) => spec_holds_dtor(t, sd) || spec_dtor_field(*rest, sd),
    }
}

pub fn dtor_field(fields: &Params, sd: &Structs) -> (r: bool)
    ensures
        r == spec_dtor_field(*fields, *sd),
    decreases fields,
{
    match fields {
        List::Nil => false,
        List::Cons((_, t), rest) => holds_dtor(*t, sd) || dtor_field(rest, sd),
    }
}

/// The models of the structs `sd` among the structs `all` of the file. A field of a struct with a destructor is a copy, at the
/// line of the struct, decision 0178.
pub open spec fn spec_structs_in(sd: Structs, all: Structs) -> StructModels
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, _)), rest) => List::Cons(
            if spec_dtor_field(fields, all) {
                Err(Refusal::Copy(l))
            } else {
                match spec_fields(fields, l) {
                    Ok(df) => Ok((k, df)),
                    Err(r) => Err(r),
                }
            },
            Box::new(spec_structs_in(*rest, all))),
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
        Expr::Finite(a) => unknown_expr(*a),
        Expr::Abs(a) => unknown_expr(*a),
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
        Expr::Bits(_, a, b, _) => unknown_expr(*a) || unknown_expr(*b),
        Expr::Fill(a, b) => unknown_expr(*a) || unknown_expr(*b),
        Expr::StaticCast(_, a) => unknown_expr(*a),
        Expr::List(args) => unknown_args(*args),
        Expr::Step(_, _, _, _) => false,
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
        Stmt::SetOwnField(_, _, e, _) => unknown_expr(e),
        Stmt::SetIndex(_, i, e, _) => unknown_expr(i) || unknown_expr(e),
        Stmt::SetFieldAt(_, i, e, _) => unknown_expr(i) || unknown_expr(e),
        Stmt::PushBack(_, e, _) => unknown_expr(e),
        Stmt::Sort(_, _) => false,
        Stmt::SortBy(_, _, _, _, e, _) => unknown_expr(e),
        Stmt::Switch(e, _, cs, _) => unknown_expr(e) || unknown_cases(*cs),
        Stmt::Call(_, _, args, _) => unknown_args(*args),
        Stmt::Exit(_) => false,
        Stmt::Assert(_, _) => false,
        Stmt::Apply(_, _, _) => false,
        Stmt::Block(b, _) => unknown_stmts(*b),
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

/// Taking the moves out of an expression keeps each node with no rule, decision 0171.
pub proof fn lemma_unmove_unknown(e: Expr)
    ensures
        unknown_expr(e) ==> unknown_expr(spec_unmove(e).0),
        (e is Call) == (spec_unmove(e).0 is Call),
        e is Call ==> spec_unmove(e).0->Call_0 == e->Call_0 && spec_unmove(e).0->Call_1 == e->Call_1 && *spec_unmove(e).0->Call_2 == spec_unmove_args(*e->Call_2).0 && spec_unmove(e).0->Call_3 == e->Call_3,
    decreases e,
{
    match e {
        Expr::Call(_, _, args, _) => lemma_unmove_args_unknown(*args),
        Expr::Construct(_, args) => lemma_unmove_args_unknown(*args),
        Expr::Wrap(a) => lemma_unmove_unknown(*a),
        Expr::Cast(_, a) => lemma_unmove_unknown(*a),
        Expr::Paren(a) => lemma_unmove_unknown(*a),
        _ => {},
    }
}

pub proof fn lemma_unmove_args_unknown(args: Args)
    ensures
        unknown_args(args) ==> unknown_args(spec_unmove_args(args).0),
    decreases args,
{
    match args {
        List::Cons(a, rest) => {
            lemma_unmove_unknown(*a);
            lemma_unmove_args_unknown(*rest);
        },
        List::Nil => {},
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

/// A return value with a node that has no rule is refused, a braced list too, decision 0175.
pub proof fn lemma_unknown_return_is_refused(e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        unknown_expr(e),
    ensures
        spec_return(e, l, all, ps, sd).is_err(),
{
    if e is List {
        lemma_unknown_lift_args_is_refused(*e->List_0, all, l, sd, 0, true);
    } else if e is Construct {
        lemma_unknown_lift_args_is_refused(*e->Construct_1, all, l, sd, 0, true);
    } else if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_unknown_lower_is_refused(e, None, false, all, l, sd, 0);
    } else {
        lemma_unknown_value_is_refused(e, all, l, sd);
    }
}

/// A local vector `v(n, x)` that holds a node with no rule is refused, decision 0185.
pub proof fn lemma_unknown_fill_local_is_refused(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        t is Vec,
        e is Fill,
        unknown_expr(e),
    ensures
        spec_local_stmt(n, t, e, l, all, env, ps, sd).is_err(),
{
    reveal(spec_local_stmt);
    let c = *e->Fill_0;
    let x = *e->Fill_1;
    if unknown_expr(c) {
        lemma_unknown_lift_is_refused(c, all, l, sd, 0, true);
    } else if spec_lift(c, all, l, sd, 0, true).is_ok() {
        lemma_unknown_lift_is_refused(x, all, l, sd, spec_lift(c, all, l, sd, 0, true).unwrap().2, true);
    }
}

/// A local std::array from a brace list that holds a node with no rule is refused, decision 0184.
pub proof fn lemma_unknown_array_local_is_refused(n: u32, t: Ty, e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        t is Seq && t->Seq_1 is Fixed,
        unknown_expr(e),
    ensures
        spec_local_stmt(n, t, e, l, all, env, ps, sd).is_err(),
{
    reveal(spec_local_stmt);
    if let Expr::List(args) = e {
        lemma_unknown_lift_args_is_refused(*args, all, l, sd, 0, true);
    }
}

#[verifier::rlimit(40)]
pub proof fn lemma_unknown_stmt_is_refused(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmt(s),
    ensures
        spec_stmt(s, all, env, ps, sd).is_err(),
    decreases s, 0nat,
{
    match s {
        Stmt::Return(e, l) => {
            reveal(spec_return_stmt);
            lemma_unmove_unknown(e);
            lemma_unknown_return_is_refused(spec_unmove(e).0, l, all, ps, sd);
            lemma_unknown_lift_is_refused(spec_unmove(e).0, all, l, sd, 0, true);
            lemma_unknown_lower_is_refused(spec_unmove(e).0, None, true, all, l, sd, 0);
        },
        Stmt::Block(b, _) => lemma_unknown_stmts_is_refused(*b, all, env, ps, sd),
        Stmt::If(c, t, f, l) => {
            if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, true);
            } else if unknown_stmts(*t) {
                lemma_unknown_stmts_is_refused(*t, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused(*f, all, env, ps, sd);
            }
        },
        Stmt::Local(n, t, e, l) => if t is Seq && t->Seq_1 is Fixed {
            lemma_unknown_array_local_is_refused(n, t, e, l, all, env, ps, sd);
        } else if t is Vec && e is Fill {
            lemma_unknown_fill_local_is_refused(n, t, e, l, all, env, ps, sd);
        } else {
            reveal(spec_local_stmt);
            if e is Call {
                if let Ok(dt) = spec_value_ty(t, l, sd) {
                    lemma_unknown_local_call_is_refused(n, dt, e->Call_0, e->Call_1, *e->Call_2, e->Call_3, all, l, ps, sd);
                }
            } else {
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            }
            // The start value of a local with no vector type reads its moves first, decision 0171.
            lemma_unmove_unknown(e);
            let e2 = spec_unmove(e).0;
            if e2 is Call {
                lemma_unmove_args_unknown(*e->Call_2);
                if let Ok(dt) = spec_value_ty(t, l, sd) {
                    lemma_unknown_local_call_is_refused(n, dt, e2->Call_0, e2->Call_1, *e2->Call_2, e2->Call_3, all, l, ps, sd);
                }
            } else {
                lemma_unknown_lift_is_refused(e2, all, l, sd, 0, true);
            }
        },
        Stmt::SetField(_, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        Stmt::SetRefField(_, _, e, l) => lemma_unknown_lift_is_refused(e, all, l, sd, 0, true),
        // The value of a write through a unique_ptr lifts after its moves, decision 0186.
        Stmt::SetOwnField(_, _, e, l) => {
            lemma_unmove_unknown(e);
            lemma_unknown_lift_is_refused(spec_unmove(e).0, all, l, sd, 0, true);
        },
        Stmt::SetIndex(_, i, e, l) => {
            if unknown_expr(i) {
                lemma_unknown_code_is_refused(i, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::SetFieldAt(_, i, e, l) => {
            if unknown_expr(i) {
                lemma_unknown_code_is_refused(i, l);
            } else {
                lemma_unknown_code_is_refused(e, l);
            }
        },
        Stmt::PushBack(_, e, l) => {
            lemma_unknown_code_is_refused(e, l);
            lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
        },
        Stmt::Sort(_, _) => {},
        Stmt::SortBy(_, _, _, _, e, l) => lemma_unknown_code_is_refused(e, l),
        Stmt::Switch(e, _, cs, l) => {
            if unknown_expr(e) {
                lemma_unknown_lift_is_refused(e, all, l, sd, 0, true);
            } else {
                lemma_unknown_cases_is_refused(*cs, all, env, ps, sd);
            }
        },
        Stmt::Call(k, nm, args, l) => {
            lemma_unmove_args_unknown(*args);
            lemma_unknown_call_stmt_is_refused(k, nm, spec_unmove_args(*args).0, l, all, ps, sd);
        },
        Stmt::Assign(_, e, l) => {
            reveal(spec_assign_stmt);
            lemma_unknown_value_is_refused(e, all, l, sd);
        },
        Stmt::While(c, _, body, l) => {
            if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, false);
            } else {
                lemma_unknown_stmts_is_refused(*body, all, env, ps, sd);
            }
        },
        Stmt::For(init, c, step, _, body, l) => {
            if unknown_stmt(*init) {
                lemma_unknown_stmt_is_refused(*init, all, env, ps, sd);
            } else if unknown_expr(c) {
                lemma_unknown_lift_is_refused(c, all, l, sd, 0, false);
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
    decreases cs, 0nat,
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
    decreases ss, 1nat,
{
    lemma_unknown_stmts_is_refused_seq(ss, all, env, ps, sd);
}

pub proof fn lemma_unknown_stmts_is_refused_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        unknown_stmts(ss),
    ensures
        spec_stmts_seq(ss, all, env, ps, sd).is_err(),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            if unknown_stmt(*s) {
                lemma_unknown_stmt_is_refused(*s, all, env, ps, sd);
            } else {
                lemma_unknown_stmts_is_refused_seq(*rest, all, spec_scope(*s, env), ps, sd);
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
    lemma_unknown_stmts_is_refused(f.body, all, f.params, spec_kept_params(f.params, spec_moves_stmts(f.body)), sd);
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
        Stmt::Block(b, _) => 1 + count_stmts(*b),
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
        DStmt::Moved(s, _) => count_dstmt(*s),
        DStmt::Gone(s, _, _) => count_dstmt(*s),
        // A bare block is a statement with its statements, and the destructors that run at the end of a block are none, decision 0178.
        DStmt::Scope(b) => 1 + count_dstmts(*b),
        DStmt::Dtors(_) => 0,
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
    reveal(spec_return_stmt);
    reveal_with_fuel(count_dstmt, 2);
}

/// A statement that moves is one Dafny statement, as the statement inside it, decision 0171.
pub proof fn lemma_moved_count(d: DStmt, ns: Names)
    ensures
        count_dstmt(spec_moved(d, ns)) == count_dstmt(d),
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_local_value_kept(n: u32, dt: DTy, e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_local_value(n, dt, e, l, all, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_local_value(n, dt, e, l, all, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_call_stmt_kept(k: u32, nm: u32, args: Args, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_call_stmt(k, nm, args, l, all, ps, sd).is_ok(),
    ensures
        count_dstmt(spec_call_stmt(k, nm, args, l, all, ps, sd).unwrap()) == 1,
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
    reveal(spec_local_stmt);
    if s->Local_1 is Vec || (s->Local_1 is Seq && s->Local_1->Seq_1 is Fixed) {
        reveal_with_fuel(count_dstmt, 2);
    } else {
        let (n, t, e, l) = (s->Local_0, s->Local_1, s->Local_2, s->Local_3);
        let dt = spec_value_ty(t, l, sd).unwrap();
        let (e2, ns) = spec_unmove(e);
        lemma_local_value_kept(n, dt, e2, l, all, ps, sd);
        lemma_moved_count(spec_local_value(n, dt, e2, l, all, ps, sd).unwrap(), ns);
    }
}

pub proof fn lemma_kept_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal(spec_assign_stmt);
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_set_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetField || s is SetRefField || s is PushBack,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_set_own_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetOwnField,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    let (n, f, l) = (s->SetOwnField_0, s->SetOwnField_1, s->SetOwnField_3);
    let (e2, ns) = spec_unmove(s->SetOwnField_2);
    let (c, d, _) = spec_lift(e2, all, l, sd, 0, true).unwrap();
    lemma_pre_count(c, DStmt::SetOwnField(n, f, d));
    lemma_moved_count(spec_pre(c, DStmt::SetOwnField(n, f, d)), ns);
    reveal_with_fuel(count_dstmt, 2);
}

pub proof fn lemma_kept_call(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Call,
    ensures
        count_dstmt(spec_stmt(s, all, env, ps, sd).unwrap()) == 1,
{
    let (k, nm, l) = (s->Call_0, s->Call_1, s->Call_3);
    let (a2, ns) = spec_unmove_args(*s->Call_2);
    lemma_call_stmt_kept(k, nm, a2, l, all, ps, sd);
    lemma_moved_count(spec_call_stmt(k, nm, a2, l, all, ps, sd).unwrap(), ns);
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
    decreases s, 0nat,
{
    match s {
        Stmt::Return(_, _) => lemma_kept_return(s, all, env, ps, sd),
        Stmt::Block(b, _) => lemma_statements_kept(*b, all, env, ps, sd),
        Stmt::Local(_, _, _, _) => lemma_kept_local(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_kept_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
        Stmt::SetOwnField(_, _, _, _) => lemma_kept_set_own_field(s, all, env, ps, sd),
        Stmt::PushBack(_, _, _) => lemma_kept_set_field(s, all, env, ps, sd),
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
    decreases cs, 0nat,
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
    decreases ss, 1nat,
{
    lemma_statements_kept_seq(ss, all, env, ps, sd);
    // The destructors at the end of a block are no statement of C++, decision 0178.
    lemma_block_end_dtors(ss, all, ps, sd);
    lemma_with_end_count(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), spec_block_end(ss, all, ps, sd), spec_last_place(ss));
}

pub proof fn lemma_statements_kept_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts_seq(ss, all, env, ps, sd).is_ok(),
    ensures
        count_dstmts(spec_stmts_seq(ss, all, env, ps, sd).unwrap()) == count_stmts(ss),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            lemma_stmt_kept(*s, all, env, ps, sd);
            lemma_statements_kept_seq(*rest, all, spec_scope(*s, env), ps, sd);
        },
        List::Nil => {},
    }
}

/// The count of two lists of statements is the sum of their counts.
pub proof fn lemma_count_append(a: DStmts, b: DStmts)
    ensures
        count_dstmts(spec_append(a, b)) == count_dstmts(a) + count_dstmts(b),
    decreases a,
{
    match a {
        List::Nil => {},
        List::Cons(_, rest) => lemma_count_append(*rest, b),
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
        DStmt::ReturnUpdate(_, k, _) => spec_callable(all, k, sd),
        DStmt::AssignCall(_, k, _) => spec_callable(all, k, sd),
        DStmt::Update(_, k, _) => spec_callable(all, k, sd),
        DStmt::UpdateAt(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::LocalUpdate(_, _, _, k, _) => spec_callable(all, k, sd),
        DStmt::CallStmt(k, _) => spec_callable(all, k, sd),
        DStmt::Pre(c, s) => calls_resolve_calls(c, all, sd) && calls_resolve_stmt(*s, all, sd),
        DStmt::Moved(s, _) => calls_resolve_stmt(*s, all, sd),
        DStmt::Gone(s, _, _) => calls_resolve_stmt(*s, all, sd),
        DStmt::Block(b) => calls_resolve(*b, all, sd),
        DStmt::Scope(b) => calls_resolve(*b, all, sd),
        DStmt::Dtors(b) => calls_resolve(*b, all, sd),
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
        List::Cons(p, rest) => (match p {
            DPre::Call(_, _, k, _) => spec_callable(all, k, sd),
            DPre::Update(_, _, _, k, _) => spec_callable(all, k, sd),
            DPre::Step(_, _, _, _, _, _) => true,
        }) && calls_resolve_calls(*rest, all, sd),
    }
}

pub proof fn lemma_append_resolves(a: DCalls, b: DCalls, all: Fns, sd: Structs)
    ensures
        calls_resolve_calls(spec_append(a, b), all, sd) == (calls_resolve_calls(a, all, sd) && calls_resolve_calls(b, all, sd)),
    decreases a,
{
    match a {
        List::Cons(_, rest) => lemma_append_resolves(*rest, b, all, sd),
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
            assert(spec_callable(all, k, sd));
            if !(spec_inline(all, k) && spec_callable(all, k, sd)) {
                let dt = spec_callee_ty(all, k, line, sd).unwrap();
                // A call that writes back runs as an update, decision 0177, and any other as a call. Each names a callable key.
                let p = if spec_callee_writes(all, k) {
                    DPre::Update(n1, dt, spec_free_callee_writebacks(all, k, *args, line).unwrap(), k, da)
                } else {
                    DPre::Call(n1, dt, k, da)
                };
                assert(calls_resolve_calls(List::Nil, all, sd));
                assert(calls_resolve_calls(List::Cons(p, Box::new(List::Nil)), all, sd));
                lemma_append_resolves(ca, List::Cons(p, Box::new(List::Nil)), all, sd);
            }
        },
        Expr::Step(_, _, _, _) => {
            assert(calls_resolve_calls(List::Nil, all, sd));
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
        Expr::Bits(_, a, b, _) => {
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
        Expr::Bits(_, a, b, _) => {
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
        Expr::Bits(_, a, b, _) => {
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
        // A call of a const virtual function is its function in place, and its arguments run no call, decision 0172.
        Expr::Call(_, _, args, _) => lemma_closed_args_run_no_call(*args, all, line, sd, n),
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

/// A `return`: the value, and with live locals the destructors, decision 0178.
pub proof fn lemma_resolves_return(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Return,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_return_stmt);
    let e = spec_unmove(s->Return_0).0;
    let l = s->Return_1;
    if !(spec_live(env, sd) is Nil) {
        lemma_resolves_dying_return(e, l, all, env, ps, sd);
    } else {
        lemma_resolves_value_return(e, l, all, ps, sd);
    }
}

/// A `return` with no live local.
pub proof fn lemma_resolves_value_return(e: Expr, l: u32, all: Fns, ps: Params, sd: Structs)
    requires
        spec_return(e, l, all, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_return(e, l, all, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    if e is List {
        lemma_lift_args_resolves(*e->List_0, all, l, sd, 0, true);
        let (c, da, _) = spec_lift_args(*e->List_0, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::Return(DExpr::SeqLit(Box::new(da))), all, sd);
    } else if e is Construct {
        lemma_lift_args_resolves(*e->Construct_1, all, l, sd, 0, true);
        let (c, da, _) = spec_lift_args(*e->Construct_1, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::Return(DExpr::Ctor(e->Construct_0, Box::new(da))), all, sd);
    } else if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_lower_resolves(e, None, false, all, l, sd, 0);
    } else {
        lemma_value_resolves(e, all, l, sd);
    }
}

/// The end of a block that the destructors leave: each destructor, then the exit. Each destructor names a method.
pub proof fn lemma_resolves_dtors_exit(ds: DStmts, l: u32, all: Fns, sd: Structs)
    requires
        calls_resolve(ds, all, sd),
    ensures
        calls_resolve(List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil)))), all, sd),
{
    reveal_with_fuel(calls_resolve, 3);
    let ex: DStmts = List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil));
    assert(calls_resolve(ex, all, sd));
    assert(calls_resolve_stmt(DStmt::Dtors(Box::new(ds)), all, sd));
}

/// A `return` with live locals: the value lifts or lowers, then the destructors run, decision 0178.
pub proof fn lemma_resolves_dying_return(e: Expr, l: u32, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_dying_return(e, l, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_dying_return(e, l, all, env, ps, sd).unwrap(), all, sd),
{
    lemma_dtor_calls_resolve(spec_live(env, sd), all, ps, sd, l);
    let ds = spec_dtor_calls(spec_live(env, sd), all, ps, sd, l).unwrap();
    lemma_resolves_dtors_exit(ds, l, all, sd);
    let tail: DStmts = List::Cons((Box::new(DStmt::Dtors(Box::new(ds))), l), Box::new(List::Cons((Box::new(DStmt::Exit), l), Box::new(List::Nil))));
    if !(e is Call) && spec_cond_calls(e, all, l, sd) {
        lemma_lower_resolves(e, None, true, all, l, sd, 0);
        let (ss, _) = spec_lower(e, None, true, all, l, sd, 0).unwrap();
        lemma_resolve_append(ss, tail, all, sd);
    } else {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetResult(d), all, sd);
        let b: DStmts = List::Cons((Box::new(spec_pre(c, DStmt::SetResult(d))), l), Box::new(tail));
        assert(calls_resolve(b, all, sd));
    }
}

pub proof fn lemma_resolves_assign(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Assign,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_assign_stmt);
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

/// A push_back runs the calls of its value before it, decision 0170, and each names a method.
pub proof fn lemma_resolves_push(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is PushBack,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 2);
    let v = s->PushBack_0;
    let e = s->PushBack_1;
    let l = s->PushBack_2;
    if e is Wrap && spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(d))), all, sd);
        lemma_pre_resolves(c, DStmt::Assign(v, DExpr::Append(Box::new(DExpr::Var(v)), Box::new(d))), all, sd);
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

pub proof fn lemma_resolves_set_own_field(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is SetOwnField,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal_with_fuel(calls_resolve_stmt, 3);
    let e = spec_unmove(s->SetOwnField_2).0;
    let l = s->SetOwnField_3;
    if spec_lift(e, all, l, sd, 0, true).is_ok() {
        lemma_lift_resolves(e, all, l, sd, 0, true);
        let (c, d, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
        lemma_pre_resolves(c, DStmt::SetOwnField(s->SetOwnField_0, s->SetOwnField_1, d), all, sd);
    }
}

/// A statement that holds no call gives a Dafny statement that holds none.
#[verifier::rlimit(60)]
pub proof fn lemma_resolves_plain(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Step || s is Assert || s is Apply || s is Unknown || s is SetIndex || s is SetFieldAt || s is Sort || s is SortBy,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
}

/// An exit with live locals runs each destructor first, decision 0178. Each destructor names a method.
pub proof fn lemma_resolves_exit(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Exit,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    if !(spec_live(env, sd) is Nil) {
        let l = s->Exit_0;
        lemma_dtor_calls_resolve(spec_live(env, sd), all, ps, sd, l);
        lemma_resolves_dtors_exit(spec_dtor_calls(spec_live(env, sd), all, ps, sd, l).unwrap(), l, all, sd);
        assert(spec_stmt(s, all, env, ps, sd) == spec_dying_exit(l, all, env, ps, sd));
    }
}

pub proof fn lemma_resolves_local(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
        s is Local,
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
{
    reveal(spec_local_stmt);
    reveal_with_fuel(calls_resolve_stmt, 3);
    let l = s->Local_3;
    // The vector arm reads the start value as it is, and the other arm with its moves taken out, decision 0171.
    let e1 = s->Local_2;
    let e2 = spec_unmove(s->Local_2).0;
    // `v(n, x)` lifts its count, then its value, decision 0185.
    if let Expr::Fill(c, x) = e1 {
        if spec_lift(*c, all, l, sd, 0, true).is_ok() {
            lemma_lift_resolves(*c, all, l, sd, 0, true);
            let (c1, _, n1) = spec_lift(*c, all, l, sd, 0, true).unwrap();
            if spec_lift(*x, all, l, sd, n1, true).is_ok() {
                lemma_lift_resolves(*x, all, l, sd, n1, true);
                lemma_append_resolves(c1, spec_lift(*x, all, l, sd, n1, true).unwrap().0, all, sd);
            }
        }
    }
    // A local std::array from a brace list lifts each value, decision 0184.
    if let Expr::List(args) = e1 {
        if spec_lift_args(*args, all, l, sd, 0, true).is_ok() {
            lemma_lift_args_resolves(*args, all, l, sd, 0, true);
        }
    }
    lemma_value_resolves(e1, all, l, sd);
    lemma_value_resolves(e2, all, l, sd);
    if let Expr::Call(k, nm, args, at) = e1 {
        if let List::Cons(_, rest) = *args {
            if spec_call_lift(k, nm, *rest, at, all, l, sd).is_ok() {
                lemma_call_lift_resolves(k, nm, *rest, at, all, l, sd);
            }
        }
    }
    if let Expr::Call(k, nm, args, at) = e2 {
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
    reveal_with_fuel(calls_resolve_stmt, 3);
    let k = s->Call_0;
    let nm = s->Call_1;
    let args = spec_unmove_args(*s->Call_2).0;
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

#[verifier::rlimit(60)]
pub proof fn lemma_stmt_calls_resolve(s: Stmt, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmt(s, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve_stmt(spec_stmt(s, all, env, ps, sd).unwrap(), all, sd),
    decreases s, 0nat,
{
    match s {
        Stmt::Return(_, _) => lemma_resolves_return(s, all, env, ps, sd),
        Stmt::Assign(_, _, _) => lemma_resolves_assign(s, all, env, ps, sd),
        Stmt::SetField(_, _, _) => lemma_resolves_set_field(s, all, env, ps, sd),
        Stmt::SetRefField(_, _, _, _) => lemma_resolves_set_ref_field(s, all, env, ps, sd),
        Stmt::SetOwnField(_, _, _, _) => lemma_resolves_set_own_field(s, all, env, ps, sd),
        Stmt::Switch(e, k, cs, l) => {
            lemma_cases_calls_resolve(*cs, all, env, ps, sd);
            lemma_lift_resolves(e, all, l, sd, 0, true);
            let (ce, de, _) = spec_lift(e, all, l, sd, 0, true).unwrap();
            lemma_pre_resolves(ce, DStmt::Match(de, k, Box::new(spec_cases(*cs, all, env, ps, sd).unwrap())), all, sd);
        },
        Stmt::Local(_, _, _, _) => lemma_resolves_local(s, all, env, ps, sd),
        Stmt::Call(_, _, _, _) => lemma_resolves_call(s, all, env, ps, sd),
        Stmt::Step(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Exit(_) => lemma_resolves_exit(s, all, env, ps, sd),
        Stmt::Block(b, _) => lemma_stmts_calls_resolve(*b, all, env, ps, sd),
        Stmt::Assert(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Apply(_, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::Unknown(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetIndex(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SetFieldAt(_, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::PushBack(_, _, _) => lemma_resolves_push(s, all, env, ps, sd),
        Stmt::Sort(_, _) => lemma_resolves_plain(s, all, env, ps, sd),
        Stmt::SortBy(_, _, _, _, _, _) => lemma_resolves_plain(s, all, env, ps, sd),
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
    decreases cs, 0nat,
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
    decreases ss, 1nat,
{
    lemma_stmts_calls_resolve_seq(ss, all, env, ps, sd);
    lemma_block_end_resolves(ss, all, ps, sd);
    lemma_with_end_resolves(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), spec_block_end(ss, all, ps, sd), spec_last_place(ss), all, sd);
}

pub proof fn lemma_stmts_calls_resolve_seq(ss: Stmts, all: Fns, env: Params, ps: Params, sd: Structs)
    requires
        spec_stmts_seq(ss, all, env, ps, sd).is_ok(),
    ensures
        calls_resolve(spec_stmts_seq(ss, all, env, ps, sd).unwrap(), all, sd),
    decreases ss, 0nat,
{
    match ss {
        List::Cons(s, rest) => {
            lemma_stmt_calls_resolve(*s, all, env, ps, sd);
            lemma_stmts_calls_resolve_seq(*rest, all, spec_scope(*s, env), ps, sd);
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

/// The locals of the moved parameters hold no call, so the block of them resolves when the body does, decision 0186.
pub proof fn lemma_param_locals_resolve(mp: List<(u32, Scalar)>, line: u32, tail: DStmts, all: Fns, sd: Structs)
    requires
        calls_resolve(tail, all, sd),
    ensures
        calls_resolve(spec_param_locals(mp, line, tail), all, sd),
    decreases mp,
{
    match mp {
        List::Nil => {},
        List::Cons((n, sc), rest) => {
            lemma_param_locals_resolve(*rest, line, tail, all, sd);
            assert(calls_resolve_stmt(DStmt::Local(n, DTy::Opt(sc), DExpr::Var(n)), all, sd));
        },
    }
}

pub proof fn lemma_param_block_resolves(mp: List<(u32, Scalar)>, line: u32, body: DStmts, all: Fns, sd: Structs)
    requires
        calls_resolve(body, all, sd),
    ensures
        calls_resolve(spec_param_block(mp, line, body), all, sd),
{
    lemma_param_locals_resolve(mp, line, body, all, sd);
    reveal_with_fuel(calls_resolve, 2);
    reveal_with_fuel(calls_resolve_stmt, 2);
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
        let ms = spec_moves_stmts(f.body);
        lemma_stmts_calls_resolve(f.body, all, f.params, spec_kept_params(f.params, ms), sd);
        lemma_param_block_resolves(spec_moved_params(f.params, ms), f.line, spec_stmts(f.body, all, f.params, spec_kept_params(f.params, ms), sd).unwrap(), all, sd);
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
        // A unique_ptr as an element of a vector, decision 0170.
        Scalar::Own(k) => DTy::Opt(Scalar::Struct(k)),
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
        Ty::F64 => Ok(DTy::Real),
        Ty::Bool => Ok(DTy::Bool),
        Ty::Seq(Scalar::Bool, _) => Err(Refusal::Element(line)),
        Ty::Seq(s, _) => Ok(DTy::Seq(s)),
        Ty::Struct(k) => Ok(DTy::Struct(k)),
        // A unique_ptr is a scalar of the model only as the element of a sequence, decision 0170.
        Ty::Opt(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Ptr(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Own(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Mut(Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::MutAfter(Scalar::Own(_)) => Err(Refusal::Element(line)),
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
        Ty::Vec(Scalar::Bool) => Err(Refusal::Element(line)),
        Ty::Vec(s) => Ok(DTy::Seq(s)),
        Ty::Enum(k) => Ok(DTy::Enum(k)),
        // An interface is a type with no value that the model can see, decision 0165.
        Ty::Iface(k) => Ok(DTy::Iface(k)),
        Ty::IfaceRef(k) => Ok(DTy::Iface(k)),
        Ty::IfaceMut(k) => Ok(DTy::Iface(k)),
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
            // An interface is a parameter only, decision 0165.
            Ty::Iface(_) => Err(Refusal::Syntax(line)),
            Ty::IfaceRef(_) => Err(Refusal::Syntax(line)),
            Ty::IfaceMut(_) => Err(Refusal::Syntax(line)),
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
            Ty::Vec(Scalar::Struct(k)) => if holds_seq(sd, k) {
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
        Scalar::Own(k) => Ty::Own(Scalar::Struct(k)),
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
            Ok(dto) => if to == Ty::F64 && from != Ty::Bool && from != Ty::F64 {
                Ok(DExpr::FromInt(Box::new(d)))
            } else if from == Ty::Bool || to == Ty::Bool || from == Ty::F64 || to == Ty::F64 {
                Err(Refusal::Convert(line))
            } else {
                Ok(DExpr::Conv(dto, Box::new(d)))
            },
        },
    }
}

pub fn loop_test(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_loop_test(*e, *all, line, *sd),
{
    match lift(e, all, line, sd, 0, false) {
        Ok((_, d, _)) => Ok(d),
        Err(r) => Err(r),
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

pub fn push_value(e: &Expr, all: &Fns, line: u32, sd: &Structs) -> (r: Result<(DCalls, DExpr), Refusal>)
    ensures
        r == spec_push_value(*e, *all, line, *sd),
{
    match e {
        Expr::Wrap(_) => match lift(e, all, line, sd, 0, true) {
            Ok((c, d, _)) => Ok((c, d)),
            Err(r) => Err(r),
        },
        _ => match translate_code(e, line) {
            Ok(d) => Ok((List::Nil, d)),
            Err(r) => Err(r),
        },
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
            Ty::Seq(_, Extent::Fixed(_)) => ret_ty(f.ret, line, sd),
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
        Expr::RealLit(d, k) => Ok((List::Nil, DExpr::RealLit(*d, *k), n)),
        Expr::Ratio(m, q) => Ok((List::Nil, ratio(*m, *q), n)),
        Expr::Enumerator(k, i) => Ok((List::Nil, DExpr::Enumerator(*k, *i), n)),
        Expr::Var(v, t) => match translate_ty(*t, line) {
            Ok(_) => Ok((List::Nil, code_var(*v, *t), n)),
            Err(r) => Err(r),
        },
        Expr::Call(k, nm, args, at) => if inline(all, *k) && callable(all, *k, sd) {
            match lift_args(args, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => Ok((ca, DExpr::FCall(*k, Box::new(da)), n1)),
            }
        } else if !open {
            Err(Refusal::Place(*at))
        } else if !callable(all, *k, sd) {
            Err(Refusal::Callee(*nm, *at))
        } else if callee_dtor(all, *k, sd) {
            Err(Refusal::Copy(line))
        } else {
            match lift_args(args, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((ca, da, n1)) => if callee_void(all, *k) { Err(Refusal::Place(*at)) } else { match callee_ty(all, *k, line, sd) {
                    Err(r) => Err(r),
                    Ok(dt) => if n1 >= 0xFFFF_FFFF {
                        Err(Refusal::Syntax(line))
                    } else if callee_writes(all, *k) {
                        if dt == DTy::Void {
                            Err(Refusal::Place(*at))
                        } else {
                            match free_callee_writebacks(all, *k, args, line) {
                                Err(r) => Err(r),
                                Ok(os) => Ok((append(ca, List::Cons(DPre::Update(n1, dt, os, *k, da), Box::new(List::Nil))), DExpr::Temp(n1), n1 + 1)),
                            }
                        }
                    } else {
                        Ok((append(ca, List::Cons(DPre::Call(n1, dt, *k, da), Box::new(List::Nil))), DExpr::Temp(n1), n1 + 1))
                    },
                } },
            }
        },
        Expr::Step(v, t, up, prefix) => if !open {
            Err(Refusal::Place(line))
        } else {
            match step_ty(*t) {
                None => Err(Refusal::Syntax(line)),
                Some(dt) => if n < 0xFFFF_FFFF {
                    Ok((List::Cons(DPre::Step(n, dt, *v, *up, *prefix, matches!(t, Ty::Mut(_))), Box::new(List::Nil)), DExpr::Temp(n), n + 1))
                } else {
                    Err(Refusal::Syntax(line))
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
        Expr::Bin(op, a, b) => if arith(*op) && (real(a, all) || real(b, all)) {
            if *op == BinOp::Rem || *op == BinOp::Div {
                Err(Refusal::Rounds(line))
            } else {
                match lift(a, all, line, sd, n, open) {
                    Err(r) => Err(r),
                    Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open) {
                        Err(r) => Err(r),
                        Ok((cb, db, n2)) => Ok((append(ca, cb), DExpr::FOp(*op, Box::new(da), Box::new(db)), n2)),
                    },
                }
            }
        } else if *op == BinOp::Div || *op == BinOp::Rem || bit_op(*op) || a.is_ptr_var() || b.is_ptr_var() {
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
        Expr::Divide(op, a, b, t) => if *t == Ty::F64 || real(a, all) || real(b, all) {
            if *op == BinOp::Div {
                match lift(a, all, line, sd, n, open) {
                    Err(r) => Err(r),
                    Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open) {
                        Err(r) => Err(r),
                        Ok((cb, db, n2)) => Ok((append(ca, cb), DExpr::FOp(*op, Box::new(da), Box::new(db)), n2)),
                    },
                }
            } else {
                Err(Refusal::Rounds(line))
            }
        } else if !(*op == BinOp::Div || *op == BinOp::Rem) {
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
        Expr::Bits(op, a, b, t) => match lift(a, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((ca, da, n1)) => match lift(b, all, line, sd, n1, open) {
                Err(r) => Err(r),
                Ok((cb, db, n2)) => match bits(*op, da, db, *t, line) {
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
            CastKind::Upcast(dk, bk) => match lift(a, all, line, sd, n, open) {
                Err(r) => Err(r),
                Ok((c, d, n1)) => Ok((c, DExpr::Upcast(*dk, *bk, Box::new(d)), n1)),
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
        Expr::Construct(k, _) if dtor_of(Ty::Struct(*k), sd).is_some() => Err(Refusal::Copy(line)),
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
        Expr::Move(_, _) => Err(Refusal::MovePlace(line)),
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
        Ty::Vec(s) => Ty::Seq(s, Extent::Dynamic),
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

pub fn unsigned(t: Ty) -> (r: bool)
    ensures
        r == is_unsigned(t),
{
    t == Ty::U8 || t == Ty::U16 || t == Ty::U32 || t == Ty::U64
}

pub fn bit_op(op: BinOp) -> (r: bool)
    ensures
        r == is_bit_op(op),
{
    op == BinOp::BitAnd || op == BinOp::BitOr
}

pub fn bits(op: BinOp, da: DExpr, db: DExpr, t: Ty, line: u32) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_bits(op, da, db, t, line),
{
    match translate_ty(t, line) {
        Err(r) => Err(r),
        Ok(dt) => if !bit_op(op) {
            Err(Refusal::Syntax(line))
        } else if !unsigned(t) {
            Err(Refusal::SignedBits(line))
        } else {
            Ok(DExpr::Conv(dt, Box::new(DExpr::BitOp(op, Box::new(DExpr::AsInt(Box::new(da))), Box::new(DExpr::AsInt(Box::new(db)))))))
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
        Expr::RealLit(d, k) => Ok(DExpr::RealLit(*d, *k)),
        Expr::Ratio(m, q) => Ok(ratio(*m, *q)),
        Expr::Abs(a) => match translate_contract(a, decl, ps, ret, bound, line, sd) {
            Ok(da) => Ok(if creal(a, decl, ps, ret, bound) {
                DExpr::Abs(Box::new(da))
            } else {
                DExpr::IntAbs(Box::new(da))
            }),
            Err(r) => Err(r),
        },
        Expr::Eps => Ok(DExpr::Eps),
        Expr::Eta => Ok(DExpr::Eta),
        Expr::DblMax => Ok(DExpr::DblMax),
        Expr::Finite(a) => match path(a, decl, ps, ret, bound, line, sd) {
            Ok((_, t)) => if t == Ty::F64 {
                Ok(DExpr::Bool(true))
            } else {
                Err(Refusal::Syntax(line))
            },
            Err(r) => Err(r),
        },
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
        Expr::Bin(op, a, b) if bit_op(*op) => if signed_operand(a, decl, ps, ret, bound, line, sd) || signed_operand(b, decl, ps, ret, bound, line, sd) {
            Err(Refusal::SignedBits(line))
        } else if boolish(a) || boolish(b) {
            Err(Refusal::Syntax(line))
        } else {
            match translate_contract(a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => Ok(DExpr::BitOp(*op, Box::new(da), Box::new(db))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            }
        },
        Expr::StaticCast(t, a) => match &**a {
            Expr::Int(v) => if integer(*t) && *v <= max_of(*t) {
                Ok(DExpr::Lit(*v))
            } else {
                Err(Refusal::ContractCast(line))
            },
            _ => match path(a, decl, ps, ret, bound, line, sd) {
                Ok((d, at)) => if fits(at, *t) {
                    translate_leaf(d, at, line)
                } else {
                    Err(Refusal::ContractCast(line))
                },
                Err(Refusal::Syntax(_)) => Err(Refusal::ContractCast(line)),
                Err(r) => Err(r),
            },
        },
        Expr::Bin(op, a, b) => if ordered(*op) && (enum_operand(a, decl, ps, ret, bound, line, sd) || enum_operand(b, decl, ps, ret, bound, line, sd)) {
            Err(Refusal::Syntax(line))
        } else {
            match translate_contract(a, decl, ps, ret, bound, line, sd) {
                Ok(da) => match translate_contract(b, decl, ps, ret, bound, line, sd) {
                    Ok(db) => {
                        let ra = creal(a, decl, ps, ret, bound);
                        let rb = creal(b, decl, ps, ret, bound);
                        let da = if rb { dreal(da) } else { da };
                        let db = if ra { dreal(db) } else { db };
                        Ok(if *op == BinOp::Div && (ra || rb) {
                            DExpr::Bin(*op, Box::new(da), Box::new(db))
                        } else {
                            binary(*op, da, db)
                        })
                    },
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
            Ok((d, t)) => match struct_key(t) {
                Some(k) => match member(sd, k, VALUE_NAME) {
                    Some((key, Some((rt, _)))) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(List::Nil)))), rt, line),
                    _ => Err(Refusal::NotPure(VALUE_NAME, line)),
                },
                None => Err(Refusal::Syntax(line)),
            },
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
                    Ok(da) => static_value(*f, da, args, decl, ps, line, sd),
                    Err(r) => Err(r),
                },
            },
            None => if fresh_member(ret, sd, *f) {
                Err(Refusal::NoObject(*f, line))
            } else {
                match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => static_value(*f, da, args, decl, ps, line, sd),
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
                None => if *f == COUNT_NAME && matches!(**args, List::Nil) && t == Ty::I64 {
                    translate_leaf(d, t, line)
                } else {
                    Err(Refusal::Syntax(line))
                },
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
                        Ok(dc) => {
                            let rb = creal(b, decl, ps, ret, bound);
                            let da = if rb { dreal(da) } else { da };
                            let dc = if rb { dreal(dc) } else { dc };
                            let db = if creal(a, decl, ps, ret, bound) || creal(c, decl, ps, ret, bound) { dreal(db) } else { db };
                            Ok(DExpr::Chain(*o1, *o2, Box::new(da), Box::new(db), Box::new(dc)))
                        },
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

pub fn signed_operand(e: &Expr, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_signed_operand(*e, *decl, *ps, ret, *bound, line, *sd),
    decreases e, 1nat,
{
    match path(e, decl, ps, ret, bound, line, sd) {
        Ok((_, t)) => integer(t) && !unsigned(t),
        Err(_) => false,
    }
}

pub fn boolish(e: &Expr) -> (r: bool)
    ensures
        r == spec_boolish(*e),
{
    match e {
        Expr::Bin(op, _, _) => !arith(*op) && !bit_op(*op),
        Expr::Chain(_, _, _, _, _) => true,
        Expr::Not(_) => true,
        Expr::Bool(_) => true,
        _ => false,
    }
}

pub fn max_of(t: Ty) -> (r: u64)
    ensures
        r == spec_max(t),
{
    match t {
        Ty::U8 => 0xff,
        Ty::U16 => 0xffff,
        Ty::U32 => 0xffff_ffff,
        Ty::I8 => 0x7f,
        Ty::I16 => 0x7fff,
        Ty::I32 => 0x7fff_ffff,
        Ty::I64 => 0x7fff_ffff_ffff_ffff,
        _ => 0xffff_ffff_ffff_ffff,
    }
}

pub fn fits(from: Ty, to: Ty) -> (r: bool)
    ensures
        r == spec_fits(from, to),
{
    integer(from) && integer(to) && if unsigned(from) {
        if unsigned(to) { width(from) <= width(to) } else { width(from) < width(to) }
    } else {
        !unsigned(to) && width(from) <= width(to)
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
            Some(t) => Ok((DExpr::Result, view_ty(t))),
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
            Ty::Iface(_) => Some((*p, *t)),
            Ty::IfaceMut(_) => Some((*p, *t)),
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
        Some((_, Ty::IfaceMut(_))) => true,
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
                Ty::IfaceMut(k) => Ty::ThisAfter(*k),
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
        Ty::IfaceMut(_) => true,
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
            Ty::Iface(k) => Some((DExpr::Var(p), k)),
            Ty::IfaceMut(k) => Some((DExpr::Var(p), k)),
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
        Ty::This(k) => Ok(DTy::Struct(k)),
        Ty::Void => Ok(DTy::Void),
        Ty::Seq(_, Extent::Fixed(_)) => translate_ty(t, line),
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
        Ty::MutSeq(Scalar::Struct(k)) => if holds_seq(sd, k) {
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
        List::Cons((n, t), rest) => {
            let pt = if holds_dtor(*t, sd) && !matches!(t, Ty::Mut(Scalar::Struct(_))) { Err(Refusal::Copy(line)) } else { param_ty(*t, line, sd) };
            match pt {
            Ok(dt) => match translate_params(rest, line, sd) {
                Ok(dr) => Ok(List::Cons((*n, dt), Box::new(dr))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
            }
        },
    }
}

pub fn signature(f: &Function, sd: &Structs) -> (r: bool)
    ensures
        r == has_signature(*f, *sd),
{
    translate_params(&f.params, f.line, sd).is_ok() && ret_ty(f.ret, f.line, sd).is_ok() && checks(f).is_none()
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
        Stmt::SetOwnField(_, _, _, l) => *l,
        Stmt::Switch(_, _, _, l) => *l,
        Stmt::Call(_, _, _, l) => *l,
        Stmt::Exit(l) => *l,
        Stmt::Assert(_, l) => *l,
        Stmt::Apply(_, _, l) => *l,
        Stmt::SetIndex(_, _, _, l) => *l,
        Stmt::SetFieldAt(_, _, _, l) => *l,
        Stmt::PushBack(_, _, l) => *l,
        Stmt::Sort(_, l) => *l,
        Stmt::SortBy(_, _, _, _, _, l) => *l,
        Stmt::Block(_, l) => *l,
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
            CondKind::Reads => Err(Refusal::Misplaced(*l)),
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

pub fn owned(o: &Expr) -> (r: Option<u32>)
    ensures
        r == spec_owned(*o),
    decreases o,
{
    match o {
        Expr::Value(a) => match &**a {
            Expr::Var(v, t) => if matches!(t, Ty::Own(_)) {
                Some(*v)
            } else {
                None
            },
            _ => None,
        },
        Expr::Cast(c, a) => if *c == CastKind::Read || *c == CastKind::NoOp {
            owned(a)
        } else {
            None
        },
        Expr::Paren(a) => owned(a),
        _ => None,
    }
}

pub fn object_target(o: &Expr, ps: &Params, line: u32) -> (r: Result<Obj, Refusal>)
    ensures
        r == spec_object_target(*o, *ps, line),
{
    match owned(o) {
        Some(v) => if get_ref(ps, v).is_some() {
            Err(Refusal::NoTarget(line))
        } else {
            Ok(Obj::Owned(v))
        },
        None => target(o, ps, line),
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
                let o = if matches!(t, Ty::IfaceMut(_)) {
                    object_target(a, ps, line)
                } else {
                    target(a, ps, line)
                };
                match o {
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

pub fn elem_object(o: &Expr) -> (r: Option<(u32, Ty, &Expr)>)
    ensures
        match r {
            Some((v, t, i)) => spec_elem_object(*o) == Some((v, t, *i)),
            None => spec_elem_object(*o) is None,
        },
    decreases o,
{
    match o {
        Expr::Value(a) => match &**a {
            Expr::Index(v, i) => match &**v {
                Expr::Var(n, t) => match t {
                    Ty::Vec(Scalar::Own(_)) => Some((*n, *t, &**i)),
                    Ty::MutSeq(Scalar::Own(_)) => Some((*n, *t, &**i)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        Expr::Cast(c, a) => if *c == CastKind::Read || *c == CastKind::NoOp {
            elem_object(a)
        } else {
            None
        },
        Expr::Paren(a) => elem_object(a),
        _ => None,
    }
}

pub fn vec_obj(v: u32, t: Ty, ps: &Params, line: u32) -> (r: Result<Obj, Refusal>)
    ensures
        r == spec_vec_obj(v, t, *ps, line),
{
    match t {
        Ty::Vec(_) => if get_ref(ps, v).is_some() {
            Err(Refusal::NoTarget(line))
        } else {
            Ok(Obj::Local(v))
        },
        Ty::MutSeq(_) => if get(ps, v) == Some(t) {
            Ok(Obj::Out(v))
        } else {
            Err(Refusal::NoTarget(line))
        },
        _ => Err(Refusal::NoTarget(line)),
    }
}

pub fn index_vars(e: &Expr) -> (r: Option<Names>)
    ensures
        r == spec_index_vars(*e),
    decreases e,
{
    match e {
        Expr::Var(n, _) => Some(List::Cons(*n, Box::new(List::Nil))),
        Expr::Lit(_, _) => Some(List::Nil),
        Expr::Int(_) => Some(List::Nil),
        Expr::Cast(_, a) => index_vars(a),
        Expr::Paren(a) => index_vars(a),
        Expr::Size(a) => index_vars(a),
        Expr::Bin(_, a, b) => match index_vars(a) {
            Some(na) => match index_vars(b) {
                Some(nb) => Some(append(na, nb)),
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

pub fn obj_named(o: Obj, ns: &Names) -> (r: bool)
    ensures
        r == spec_obj_named(o, *ns),
{
    match o {
        Obj::Local(n) => has(ns, n),
        Obj::Out(n) => has(ns, n),
        Obj::Owned(n) => has(ns, n),
        Obj::Object => false,
    }
}

pub fn writes_name(os: &Objs, ns: &Names) -> (r: bool)
    ensures
        r == spec_writes_name(*os, *ns),
    decreases os,
{
    match os {
        List::Nil => false,
        List::Cons(o, rest) => obj_named(*o, ns) || writes_name(rest, ns),
    }
}

pub fn call_elem(key: u32, name: u32, args: &Args, line: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Option<Result<DStmt, Refusal>>)
    ensures
        r == spec_call_elem(key, name, *args, line, *all, *ps, *sd),
{
    match find(all, key) {
        Some(f) => if matches!(head_ty(&f.params), Some(Ty::IfaceMut(_))) {
            match args {
                List::Cons(a, rest) => match elem_object(a) {
                    Some((v, t, i)) => Some(match vec_obj(v, t, ps, line) {
                        Err(r) => Err(r),
                        Ok(vo) => match writebacks(rest, &tail(&f.params), ps, line) {
                            Err(r) => Err(r),
                            Ok(os) => match index_vars(i) {
                                None => Err(Refusal::IndexWritten(line)),
                                Some(ns) => if has(&ns, v) || writes_name(&os, &ns) {
                                    Err(Refusal::IndexWritten(line))
                                } else {
                                    match translate_code(i, line) {
                                        Err(r) => Err(r),
                                        Ok(di) => match call_lift(key, name, args, line, all, line, sd) {
                                            Ok((c, da)) => Ok(pre(c, DStmt::UpdateAt(vo, Box::new(di), os, key, da))),
                                            Err(r) => Err(r),
                                        },
                                    }
                                },
                            },
                        },
                    }),
                    None => None,
                },
                List::Nil => None,
            }
        } else {
            None
        },
        None => None,
    }
}

pub fn call_stmt(key: u32, name: u32, args: &Args, line: u32, all: &Fns, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_call_stmt(key, name, *args, line, *all, *ps, *sd),
{
    if callee_dtor(all, key, sd) {
        return Err(Refusal::Copy(line));
    }
    let elem = if callee_writes(all, key) {
        call_elem(key, name, args, line, all, ps, sd)
    } else {
        None
    };
    if let Some(r) = elem {
        r
    } else if callee_writes(all, key) {
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
    decreases s, 0nat,
{
    proof {
        reveal(spec_return_stmt);
        reveal(spec_local_stmt);
        reveal(spec_assign_stmt);
    }
    match s {
        Stmt::Return(e, l) => {
            let (e2, ns) = unmove(e);
            match move_check(&ns, &var_names(e), ps, true, *l) {
                Some(r) => Err(r),
                None => if dtor_copy(&e2, sd) {
                    Err(Refusal::Copy(*l))
                } else if matches!(live(env, sd), List::Nil) {
                    translate_return(&e2, *l, all, ps, sd)
                } else {
                    dying_return(&e2, *l, all, env, ps, sd)
                },
            }
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
        Stmt::Local(n, Ty::Vec(s), e, l) => if holds_dtor(Ty::Vec(*s), sd) { Err(Refusal::Copy(*l)) } else { match translate_value_ty(Ty::Vec(*s), *l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match e {
                Expr::Call(k, nm, args, at) => local_call(*n, dt, *k, *nm, args, *at, all, *l, ps, sd),
                Expr::Copy(a, from, _) => if seq_elem(*from) == Some(*s) && match &**a {
                    Expr::Var(w, _) => get(env, *w).is_some() || get(ps, *w).is_some(),
                    _ => false,
                } {
                    match lift(e, all, *l, sd, 0, true) {
                        Ok((c, d, _)) => Ok(pre(c, DStmt::Local(*n, dt, d))),
                        Err(r) => Err(r),
                    }
                } else {
                    Err(Refusal::VecLocal(*l))
                },
                Expr::EmptyVec => Ok(DStmt::Local(*n, dt, DExpr::EmptySeq)),
                Expr::Fill(c, x) => match lift(c, all, *l, sd, 0, true) {
                    Err(r) => Err(r),
                    Ok((c1, dc, n1)) => match lift(x, all, *l, sd, n1, true) {
                        Err(r) => Err(r),
                        Ok((c2, dx, _)) => Ok(pre(append(c1, c2), DStmt::Local(*n, dt, DExpr::SeqFill(Box::new(dc), Box::new(dx))))),
                    },
                },
                Expr::Move(w, _) => match get(ps, *w) {
                    Some(Ty::MutSeq(s2)) => if s2 == *s {
                        Ok(DStmt::Gone(Box::new(DStmt::Local(*n, dt, DExpr::Out(*w))), *w, true))
                    } else {
                        Err(Refusal::VecLocal(*l))
                    },
                    Some(_) => Err(Refusal::WriteParam(*w, *l)),
                    None => match get(env, *w) {
                        Some(Ty::Vec(s2)) => if s2 == *s {
                            Ok(DStmt::Gone(Box::new(DStmt::Local(*n, dt, DExpr::Var(*w))), *w, false))
                        } else {
                            Err(Refusal::VecLocal(*l))
                        },
                        _ => Err(Refusal::VecLocal(*l)),
                    },
                },
                _ => Err(Refusal::VecLocal(*l)),
            },
        } },
        Stmt::Local(n, Ty::Seq(s, Extent::Fixed(k)), e, l) => if holds_dtor(Ty::Seq(*s, Extent::Fixed(*k)), sd) { Err(Refusal::Copy(*l)) } else { match e {
            Expr::List(args) => if count_args(args) as u64 != *k {
                Err(Refusal::BraceLen(count_args(args), extent32(*k), *l))
            } else {
                match translate_ty(Ty::Seq(*s, Extent::Fixed(*k)), *l) {
                    Err(r) => Err(r),
                    Ok(dt) => match lift_args(args, all, *l, sd, 0, true) {
                        Ok((c, da, _)) => Ok(pre(c, DStmt::Local(*n, dt, DExpr::SeqLit(Box::new(da))))),
                        Err(r) => Err(r),
                    },
                }
            },
            _ => Err(Refusal::SeqParam(*l)),
        } },
        Stmt::Local(n, t, e, l) => match translate_value_ty(*t, *l, sd) {
            Err(r) => Err(r),
            Ok(dt) => match dtor_local(*t, e, all, sd, *l) {
                Some(r) => Err(r),
                None => {
                    let (e2, ns) = unmove(e);
                    match move_check(&ns, &var_names(e), ps, false, *l) {
                        Some(r) => Err(r),
                        None => match local_value(*n, dt, &e2, *l, all, ps, sd) {
                            Ok(d) => Ok(moved(d, ns)),
                            Err(r) => Err(r),
                        },
                    }
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
                Expr::Call(k, nm, args, at) => if callee_dtor(all, *k, sd) {
                    Err(Refusal::Copy(*l))
                } else if callee_writes(all, *k) {
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
        Stmt::Step(n, t, up, l) => if *t == Ty::F64 {
            Err(Refusal::Rounds(*l))
        } else if get(ps, *n).is_some() && !is_mut(ps, *n) {
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
                Ok(dec) => match loop_test(c, all, *l, sd) {
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
                        Ok(di) => match loop_test(c, all, *l, sd) {
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
        Stmt::SetOwnField(n, f, e, l) => if get(ps, *n).is_some() {
            Err(Refusal::WriteParam(*n, *l))
        } else {
            match get(env, *n) {
                Some(Ty::Own(Scalar::Struct(k))) => match field_ty(sd, k, *f) {
                    Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(*l)),
                    Some(_) => {
                        let (e2, ns) = unmove(e);
                        match move_check(&ns, &List::Cons(*n, Box::new(var_names(e))), ps, false, *l) {
                            Some(r) => Err(r),
                            None => match lift(&e2, all, *l, sd, 0, true) {
                                Ok((c, d, _)) => Ok(moved(pre(c, DStmt::SetOwnField(*n, *f, d)), ns)),
                                Err(r) => Err(r),
                            },
                        }
                    },
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::Syntax(*l)),
            }
        },
        Stmt::Switch(e, k, cs, l) => match lift(e, all, *l, sd, 0, true) {
            Ok((c, d, _)) => match translate_cases(cs, all, env, ps, sd) {
                Ok(dc) => Ok(pre(c, DStmt::Match(d, *k, Box::new(dc)))),
                Err(r) => Err(r),
            },
            Err(r) => Err(r),
        },
        Stmt::Call(k, nm, args, l) => {
            let (a2, ns) = unmove_args(args);
            match move_check(&ns, &var_names_args(args), ps, false, *l) {
                Some(r) => Err(r),
                None => match call_stmt(*k, *nm, &a2, *l, all, ps, sd) {
                    Ok(d) => Ok(moved(d, ns)),
                    Err(r) => Err(r),
                },
            }
        },
        Stmt::Exit(l) => if matches!(live(env, sd), List::Nil) {
            Ok(DStmt::Exit)
        } else {
            dying_exit(*l, all, env, ps, sd)
        },
        Stmt::Block(b, _) => match translate_stmts(b, all, env, ps, sd) {
            Ok(db) => Ok(DStmt::Scope(Box::new(db))),
            Err(r) => Err(r),
        },
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
            None => match get(env, *v) {
                Some(Ty::Vec(_)) => match translate_code(i, *l) {
                    Ok(di) => match translate_code(e, *l) {
                        Ok(de) => Ok(DStmt::Assign(*v, DExpr::SetAt(Box::new(DExpr::Var(*v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                Some(Ty::Seq(_, Extent::Fixed(_))) => match translate_code(i, *l) {
                    Ok(di) => match translate_code(e, *l) {
                        Ok(de) => Ok(DStmt::Assign(*v, DExpr::SetAt(Box::new(DExpr::Var(*v)), Box::new(di), Box::new(de)))),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(*l)),
            },
        },
        Stmt::SetFieldAt(f, i, e, l) => match self_param(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match field_ty(sd, k, *f) {
                    Some(Ty::Seq(_, _)) => match translate_code(i, *l) {
                        Ok(di) => match translate_code(e, *l) {
                            Ok(de) => Ok(DStmt::SetField(*f, DExpr::SetAt(Box::new(DExpr::Field(Box::new(DExpr::After), *f)), Box::new(di), Box::new(de)))),
                            Err(r) => Err(r),
                        },
                        Err(r) => Err(r),
                    },
                    Some(_) => Err(Refusal::Syntax(*l)),
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::WriteParam(p, *l)),
            },
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::PushBack(v, e, l) => match get(ps, *v) {
            Some(Ty::MutSeq(_)) => match push_value(e, all, *l, sd) {
                Ok((c, de)) => Ok(pre(c, DStmt::SetOut(*v, DExpr::Append(Box::new(DExpr::Out(*v)), Box::new(de))))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(*v, *l)),
            None => match get(env, *v) {
                Some(Ty::Vec(_)) => match push_value(e, all, *l, sd) {
                    Ok((c, de)) => Ok(pre(c, DStmt::Assign(*v, DExpr::Append(Box::new(DExpr::Var(*v)), Box::new(de))))),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(*l)),
            },
        },
        Stmt::Sort(v, l) => match get(ps, *v) {
            Some(Ty::MutSeq(s)) => sort(DExpr::Out(*v), s, *l),
            Some(_) => Err(Refusal::WriteParam(*v, *l)),
            None => match get(env, *v) {
                Some(Ty::Vec(s)) => sort(DExpr::Var(*v), s, *l),
                _ => Err(Refusal::SortForm(*l)),
            },
        },
        Stmt::SortBy(v, a, b, t, e, l) => match get(ps, *v) {
            Some(Ty::MutSeq(s)) => sort_by(DExpr::Out(*v), s, *a, *b, *t, e, *l),
            Some(_) => Err(Refusal::WriteParam(*v, *l)),
            None => match get(env, *v) {
                Some(Ty::Vec(s)) => sort_by(DExpr::Var(*v), s, *a, *b, *t, e, *l),
                _ => Err(Refusal::SortForm(*l)),
            },
        },
        Stmt::Unknown(k, l) => Err(Refusal::Construct(*k, *l)),
    }
}

pub fn translate_cases(cs: &Cases, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DCases, Refusal>)
    ensures
        r == spec_cases(*cs, *all, *env, *ps, *sd),
    decreases cs, 0nat,
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
    decreases ss, 1nat,
{
    match translate_stmts_seq(ss, all, env, ps, sd) {
        Err(r) => Err(r),
        Ok(ds) => with_end(ds, block_end(ss, all, ps, sd), last_place(ss)),
    }
}

pub fn with_end(ds: DStmts, end: Result<Option<DStmt>, Refusal>, place: u32) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_with_end(ds, end, place),
{
    match end {
        Err(r) => Err(r),
        Ok(None) => Ok(ds),
        Ok(Some(d)) => Ok(append(ds, List::Cons((Box::new(d), place), Box::new(List::Nil)))),
    }
}

pub fn translate_stmts_seq(ss: &Stmts, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmts, Refusal>)
    ensures
        r == spec_stmts_seq(*ss, *all, *env, *ps, *sd),
    decreases ss, 0nat,
{
    match ss {
        List::Nil => Ok(List::Nil),
        List::Cons(s, rest) => match write_check(s, all, ps, sd) {
            Some(r) => Err(r),
            None => match translate_stmt(s, all, env, ps, sd) {
                Ok(d) => match translate_stmts_seq(rest, all, &scope(s, env), ps, sd) {
                    Ok(dr) => Ok(List::Cons((Box::new(d), place(s)), Box::new(dr))),
                    Err(r) => Err(r),
                },
                Err(r) => Err(r),
            },
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
        Expr::Finite(a) => has_result(a),
        Expr::Abs(a) => has_result(a),
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
            CondKind::Reads => Err(Refusal::Construct(READS_NAME, *l)),
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
        Stmt::Block(b, _) => twice_stmts(seen, b),
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

pub fn moves_stmts(ss: &Stmts) -> (r: Names)
    ensures
        r == spec_moves_stmts(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(moves_stmt(s), moves_stmts(rest)),
    }
}

pub fn moves_stmt(s: &Stmt) -> (r: Names)
    ensures
        r == spec_moves_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Local(_, _, e, _) => unmove(e).1,
        Stmt::Call(_, _, args, _) => unmove_args(args).1,
        Stmt::SetOwnField(_, _, e, _) => unmove(e).1,
        Stmt::If(_, t, f, _) => append(moves_stmts(t), moves_stmts(f)),
        Stmt::While(_, _, body, _) => moves_stmts(body),
        Stmt::For(init, _, step, _, body, _) => append(moves_stmt(init), append(moves_stmt(step), moves_stmts(body))),
        Stmt::Switch(_, _, cs, _) => moves_cases(cs),
        Stmt::RangeFor(_, _, _, _, _, body, _) => moves_stmts(body),
        Stmt::Block(b, _) => moves_stmts(b),
        _ => List::Nil,
    }
}

pub fn moves_cases(cs: &Cases) -> (r: Names)
    ensures
        r == spec_moves_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(moves_stmts(body), moves_cases(rest)),
    }
}

pub fn moved_params(ps: &Params, ms: &Names) -> (r: List<(u32, Scalar)>)
    ensures
        r == spec_moved_params(*ps, *ms),
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Own(s) => if has(ms, *n) {
                List::Cons((*n, *s), Box::new(moved_params(rest, ms)))
            } else {
                moved_params(rest, ms)
            },
            _ => moved_params(rest, ms),
        },
    }
}

pub fn kept_params(ps: &Params, ms: &Names) -> (r: Params)
    ensures
        r == spec_kept_params(*ps, *ms),
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => if matches!(t, Ty::Own(_)) && has(ms, *n) {
            kept_params(rest, ms)
        } else {
            List::Cons((*n, *t), Box::new(kept_params(rest, ms)))
        },
    }
}

pub fn param_locals(mp: &List<(u32, Scalar)>, line: u32, tail: DStmts) -> (r: DStmts)
    ensures
        r == spec_param_locals(*mp, line, tail),
    decreases mp,
{
    match mp {
        List::Nil => tail,
        List::Cons((n, s), rest) => List::Cons((Box::new(DStmt::Local(*n, DTy::Opt(*s), DExpr::Var(*n))), line), Box::new(param_locals(rest, line, tail))),
    }
}

pub fn param_block(mp: &List<(u32, Scalar)>, line: u32, body: DStmts) -> (r: DStmts)
    ensures
        r == spec_param_block(*mp, line, body),
{
    match mp {
        List::Nil => body,
        _ => List::Cons((Box::new(DStmt::Scope(Box::new(param_locals(mp, line, body)))), line), Box::new(List::Nil)),
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
                        None => {
                            let ms = moves_stmts(&f.body);
                            match translate_stmts(&f.body, all, &f.params, &kept_params(&f.params, &ms), sd) {
                                Err(r) => Err(r),
                                Ok(body) => Ok((req, ens, dec, param_block(&moved_params(&f.params, &ms), f.line, body))),
                            }
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
        DExpr::RealLit(x0, x1) => DExpr::RealLit(*x0, *x1),
        DExpr::FOp(x0, x1, x2) => DExpr::FOp(*x0, Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::Abs(x0) => DExpr::Abs(Box::new(copy_dexpr(x0))),
        DExpr::FromInt(x0) => DExpr::FromInt(Box::new(copy_dexpr(x0))),
        DExpr::Upcast(x0, x1, x2) => DExpr::Upcast(*x0, *x1, Box::new(copy_dexpr(x2))),
        DExpr::Lemma(x0, x1, x2) => DExpr::Lemma(*x0, Box::new(copy_dargs(x1)), Box::new(copy_dexpr(x2))),
        DExpr::Let(x0, x1, x2, x3) => DExpr::Let(*x0, *x1, Box::new(copy_dexpr(x2)), Box::new(copy_dexpr(x3))),
        DExpr::BitOp(x0, x1, x2) => DExpr::BitOp(*x0, Box::new(copy_dexpr(x1)), Box::new(copy_dexpr(x2))),
        DExpr::SeqLit(x0) => DExpr::SeqLit(Box::new(copy_dargs(x0))),
        DExpr::EmptySeq => DExpr::EmptySeq,
        DExpr::SeqFill(x0, x1) => DExpr::SeqFill(Box::new(copy_dexpr(x0)), Box::new(copy_dexpr(x1))),
        DExpr::IntAbs(x0) => DExpr::IntAbs(Box::new(copy_dexpr(x0))),
        DExpr::Eps => DExpr::Eps,
        DExpr::Eta => DExpr::Eta,
        DExpr::DblMax => DExpr::DblMax,
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

pub fn pure_value(body: &DStmts, all: &Fns) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_value(*body, *all),
    decreases body,
{
    match body {
        List::Cons((s, _), rest) => match &**s {
            DStmt::Return(d) => match &**rest {
                List::Nil => Some(copy_dexpr(d)),
                _ => None,
            },
            DStmt::ReturnCall(k, da) => match &**rest {
                List::Nil => if inline(all, *k) {
                    Some(DExpr::FCall(*k, Box::new(copy_dargs(da))))
                } else {
                    None
                },
                _ => None,
            },
            DStmt::Apply(f, da) => match pure_value(rest, all) {
                Some(e) => Some(DExpr::Lemma(*f, Box::new(copy_dargs(da)), Box::new(e))),
                None => None,
            },
            DStmt::Local(n, dt, d) => match pure_value(rest, all) {
                Some(e) => Some(DExpr::Let(*n, *dt, Box::new(copy_dexpr(d)), Box::new(e))),
                None => None,
            },
            DStmt::LocalCall(n, dt, k, da) => if inline(all, *k) {
                match pure_value(rest, all) {
                    Some(e) => Some(DExpr::Let(*n, *dt, Box::new(DExpr::FCall(*k, Box::new(copy_dargs(da)))), Box::new(e))),
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        },
        List::Nil => None,
    }
}

pub fn pure_body(ps: &Params, body: &DStmts, all: &Fns, stat: bool) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_body(*ps, *body, *all, stat),
{
    if (this_param(ps).is_some() || stat) && !mutates(ps) {
        pure_value(body, all)
    } else {
        None
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
        Some(_) => link(f, ens),
        None => if const_virtual(f) {
            link(f, ens)
        } else {
            ens
        },
    }
}

pub fn virtual_of(f: &Function) -> (r: Option<u32>)
    ensures
        r == spec_virtual(*f),
{
    match head_ty(&f.params) {
        Some(Ty::Iface(k)) => Some(k),
        Some(Ty::IfaceMut(k)) => Some(k),
        _ => None,
    }
}

pub fn const_virtual(f: &Function) -> (r: bool)
    ensures
        r == spec_const_virtual(*f),
{
    matches!(head_ty(&f.params), Some(Ty::Iface(_)))
}

pub fn unmark(ms: &Members) -> (r: Members)
    ensures
        r == spec_unmark(*ms),
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, _)), rest) => List::Cons((*n, (*k, None)), Box::new(unmark(rest))),
    }
}

pub fn copy_members(ms: &Members) -> (r: Members)
    ensures
        r == *ms,
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, p)), rest) => {
            let c = match p {
                Some((t, mps)) => Some((*t, copy(mps))),
                None => None,
            };
            List::Cons((*n, (*k, c)), Box::new(copy_members(rest)))
        },
    }
}

pub fn from_key(ms: &Members, key: u32) -> (r: Members)
    ensures
        r == spec_from(*ms, key),
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (k, p)), rest) => if *k == key {
            unmark(ms)
        } else {
            let c = match p {
                Some((t, mps)) => Some((*t, copy(mps))),
                None => None,
            };
            List::Cons((*n, (*k, c)), Box::new(from_key(rest, key)))
        },
    }
}

pub fn above(sd: &Structs, b: u32, key: u32) -> (r: Structs)
    ensures
        r == spec_above(*sd, b, key),
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => if *k == b {
            List::Cons((*k, (*l, copy(fields), from_key(ms, key))), Box::new(above(rest, b, key)))
        } else {
            List::Cons((*k, (*l, copy(fields), copy_members(ms))), Box::new(above(rest, b, key)))
        },
    }
}

pub fn member_name(ms: &Members, key: u32) -> (r: Option<u32>)
    ensures
        r == spec_member_name(*ms, key),
    decreases ms,
{
    match ms {
        List::Nil => None,
        List::Cons((n, (k, _)), rest) => if *k == key {
            Some(*n)
        } else {
            member_name(rest, key)
        },
    }
}

pub fn at_or_after(ms: &Members, key: u32, g: u32) -> (r: bool)
    ensures
        r == spec_at_or_after(*ms, key, g),
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((n, (k, _)), rest) => if *k == key {
            get_ref(ms, g).is_some()
        } else if *n == g {
            false
        } else {
            at_or_after(rest, key, g)
        },
    }
}

pub fn late(f: &Function, sd: &Structs, r: Refusal) -> (out: Refusal)
    ensures
        out == spec_late(*f, *sd, r),
{
    match virtual_of(f) {
        Some(b) => match r {
            Refusal::NotPure(g, l) => match get_ref(sd, b) {
                Some((_, _, ms)) => if at_or_after(ms, f.name, g) {
                    match member_name(ms, f.name) {
                        Some(n) => Refusal::Later(b, n, g, l),
                        None => r,
                    }
                } else {
                    r
                },
                None => r,
            },
            _ => r,
        },
        None => r,
    }
}

pub fn translate_inside_of(f: &Function, all: &Fns, sd: &Structs) -> (r: Result<(DConds, DConds, DConds, DStmts), Refusal>)
    ensures
        r == spec_inside_of(*f, *all, *sd),
{
    let inside = match virtual_of(f) {
        Some(b) => if f.trusted {
            let view = above(sd, b, f.name);
            translate_inside(f, all, &view)
        } else {
            translate_inside(f, all, sd)
        },
        None => translate_inside(f, all, sd),
    };
    match inside {
        Ok(x) => Ok(x),
        Err(r) => Err(late(f, sd, r)),
    }
}

pub fn link(f: &Function, ens: DConds) -> (r: DConds)
    ensures
        r == spec_link(*f, ens),
{
    append(
        ens,
        List::Cons((DExpr::Bin(BinOp::Eq, Box::new(DExpr::Result), Box::new(DExpr::FCall(f.name, Box::new(param_args(&f.params))))), f.line), Box::new(List::Nil)),
    )
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
        Ty::Iface(k) => Some(k),
        Ty::IfaceRef(k) => Some(k),
        Ty::IfaceMut(k) => Some(k),
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
        Some(f) => if !signature(f, sd) {
            None
        } else if const_virtual(f) {
            if !strict {
                Some((f.ret, copy(&f.params)))
            } else {
                match translate_inside_of(f, all, sd) {
                    Ok(_) => Some((f.ret, copy(&f.params))),
                    Err(_) => None,
                }
            }
        } else if f.trusted {
            None
        } else if strict {
            match translate_inside(f, all, sd) {
                Ok((_, _, _, body)) => match pure_body(&f.params, &body, all, static_key(sd, f.name)) {
                    Some(_) => Some((f.ret, copy(&f.params))),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match translate_stmts(&f.body, all, &f.params, &f.params, sd) {
                Ok(body) => match pure_body(&f.params, &body, all, static_key(sd, f.name)) {
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
            Ok(ret) => match checks(f) {
                Some(r) => Model::Refused(r),
                None => match braces(&f.body, fixed(f.ret)) {
                Some(r) => Model::Bare(f.name, ps, ret, r),
                None => match translate_inside_of(f, all, sd) {
                    Err(r) => Model::Bare(f.name, ps, ret, r),
                    Ok((req, ens, dec, body)) => {
                        let pure = pure_body(&f.params, &body, all, static_key(sd, f.name));
                        let ensures = ret_len(f.ret, f.line, linked(f, ens, &pure));
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
        List::Cons((n, t), rest) => match if matches!(t, Ty::Opt(Scalar::Struct(_)) | Ty::Ptr(_) | Ty::F64) || (matches!(t, Ty::Own(_)) && !matches!(t, Ty::Own(Scalar::Struct(_)))) { Err(Refusal::Element(line)) } else { translate_ty(*t, line) } {
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
{
    translate_structs_in(sd, sd)
}

pub fn translate_structs_in(sd: &Structs, all: &Structs) -> (r: StructModels)
    ensures
        r == spec_structs_in(*sd, *all),
    decreases sd,
{
    match sd {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, _)), rest) => {
            let m = if dtor_field(fields, all) {
                Err(Refusal::Copy(*l))
            } else {
                match translate_fields(fields, *l) {
                    Ok(df) => Ok((*k, df)),
                    Err(r) => Err(r),
                }
            };
            List::Cons(m, Box::new(translate_structs_in(rest, all)))
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

pub fn same_tys(a: &Params, b: &Params) -> (r: bool)
    ensures
        r == spec_same_tys(*a, *b),
    decreases a,
{
    match a {
        List::Nil => matches!(b, List::Nil),
        List::Cons((_, ta), ra) => match b {
            List::Cons((_, tb), rb) => *ta == *tb && same_tys(ra, rb),
            List::Nil => false,
        },
    }
}

pub fn head_ty(ps: &Params) -> (r: Option<Ty>)
    ensures
        r == spec_head_ty(*ps),
{
    match ps {
        List::Cons((_, t), _) => Some(*t),
        List::Nil => None,
    }
}

pub fn overrides_fn(fb: &Function, fd: &Function, d: u32, b: u32) -> (r: bool)
    ensures
        r == spec_overrides_fn(*fb, *fd, d, b),
{
    ((head_ty(&fb.params) == Some(Ty::Iface(b)) && head_ty(&fd.params) == Some(Ty::This(d))) || (head_ty(&fb.params) == Some(Ty::IfaceMut(b))
        && head_ty(&fd.params) == Some(Ty::ThisMut(d)))) && fb.ret == fd.ret && same_tys(&tail(&fb.params), &tail(&fd.params))
}

pub fn check(fb: &Function, fd: &Function, sd: &Structs) -> (r: Result<DOverride, Refusal>)
    ensures
        r == spec_check(*fb, *fd, *sd),
{
    match translate_params(&tail(&fd.params), fd.line, sd) {
        Err(r) => Err(r),
        Ok(ps) => match ret_ty(fd.ret, fd.line, sd) {
            Err(r) => Err(r),
            Ok(ret) => match translate_conds(&fb.conds, CondKind::Requires, &fd.params, fd.ret, sd) {
                Err(r) => Err(r),
                Ok(rq) => match translate_conds(&fb.conds, CondKind::Ensures, &fd.params, fd.ret, sd) {
                    Err(r) => Err(r),
                    Ok(en) => match translate_conds(&fd.conds, CondKind::Requires, &fd.params, fd.ret, sd) {
                        Err(r) => Err(r),
                        Ok(own) => match translate_conds(&fd.conds, CondKind::Ensures, &fd.params, fd.ret, sd) {
                            Err(r) => Err(r),
                            Ok(promise) => Ok(DOverride { base: fb.name, derived: fd.name, params: ps, ret, requires: rq, ensures: en, own, promise }),
                        },
                    },
                },
            },
        },
    }
}

pub fn translate_override(d: u32, b: u32, n: u32, bk: u32, line: u32, all: &Fns, sd: &Structs) -> (r: Result<DOverride, Refusal>)
    ensures
        r == spec_override(d, b, n, bk, line, *all, *sd),
{
    match member(sd, d, n) {
        None => Err(Refusal::NoOverride(d, b, n, line)),
        Some((dk, pure)) => match find(all, bk) {
            None => Err(Refusal::NoOverride(d, b, n, line)),
            Some(fb) => match find(all, dk) {
                None => Err(Refusal::NoOverride(d, b, n, line)),
                Some(fd) => if !overrides_fn(fb, fd, d, b) {
                    Err(Refusal::NoOverride(d, b, n, line))
                } else if const_virtual(fb) && pure.is_none() {
                    Err(Refusal::Unchecked(d, b, n, line))
                } else if !const_virtual(fb) && !matches!(translate_function(fd, all, sd), Model::Full(_)) {
                    Err(Refusal::NoMethod(d, b, n, line))
                } else {
                    match translate_inside_of(fb, all, sd) {
                        Err(r) => Err(r),
                        Ok(_) => check(fb, fd, sd),
                    }
                },
            },
        },
    }
}

pub fn override_each(d: u32, b: u32, ms: &Members, line: u32, all: &Fns, sd: &Structs) -> (r: Result<DOverrides, Refusal>)
    ensures
        r == spec_override_each(d, b, *ms, line, *all, *sd),
    decreases ms,
{
    match ms {
        List::Nil => Ok(List::Nil),
        List::Cons((n, (bk, _)), rest) => match translate_override(d, b, *n, *bk, line, all, sd) {
            Err(r) => Err(r),
            Ok(o) => match override_each(d, b, rest, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(List::Cons(o, Box::new(os))),
            },
        },
    }
}

pub fn keyed(ms: &Members, key: u32) -> (r: bool)
    ensures
        r == spec_keyed(*ms, key),
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (k, _)), rest) => *k == key || keyed(rest, key),
    }
}

pub fn listed(fs: &Fns, b: u32, ms: &Members) -> (r: bool)
    ensures
        r == spec_listed(*fs, b, *ms),
    decreases fs,
{
    match fs {
        List::Nil => true,
        List::Cons(f, rest) => (virtual_of(f) != Some(b) || keyed(ms, f.name)) && listed(rest, b, ms),
    }
}

pub fn upcast(d: u32, b: u32, line: u32, all: &Fns, sd: &Structs) -> (r: Result<DUpcast, Refusal>)
    ensures
        r == spec_upcast(d, b, line, *all, *sd),
{
    match get_ref(sd, b) {
        None => Err(Refusal::Syntax(line)),
        Some((bl, _, ms)) => if !listed(all, b, ms) {
            Err(Refusal::Overload(b, *bl))
        } else {
            match override_each(d, b, ms, line, all, sd) {
                Err(r) => Err(r),
                Ok(os) => Ok(DUpcast { derived: d, base: b, overrides: os }),
            }
        },
    }
}

pub fn upcasts_of(d: u32, bs: &Names, line: u32, all: &Fns, sd: &Structs) -> (r: List<Result<DUpcast, Refusal>>)
    ensures
        r == spec_upcasts_of(d, *bs, line, *all, *sd),
    decreases bs,
{
    match bs {
        List::Nil => List::Nil,
        List::Cons(b, rest) => List::Cons(upcast(d, *b, line, all, sd), Box::new(upcasts_of(d, rest, line, all, sd))),
    }
}

pub fn upcasts(bases: &List<(u32, (Names, bool))>, all: &Fns, sd: &Structs) -> (r: List<Result<DUpcast, Refusal>>)
    ensures
        r == spec_upcasts(*bases, *all, *sd),
    decreases bases,
{
    match bases {
        List::Nil => List::Nil,
        List::Cons((d, (bs, fin)), rest) => match get_ref(sd, *d) {
            None => List::Cons(Err(Refusal::Syntax(0)), Box::new(upcasts(rest, all, sd))),
            Some((line, _, _)) => if !*fin {
                List::Cons(Err(Refusal::NotFinal(*d, *line)), Box::new(upcasts(rest, all, sd)))
            } else {
                append(upcasts_of(*d, bs, *line, all, sd), upcasts(rest, all, sd))
            },
        },
    }
}

/// The upcasts of the unit, each with the check of each override, decision 0165. The checks read the table of the unit, as the models
/// of its functions do.
pub fn translate_overrides(bases: &List<(u32, (Names, bool))>, all: &Fns, sd: &Structs) -> (r: List<Result<DUpcast, Refusal>>)
    ensures
        r == spec_upcasts(*bases, *all, spec_marked(*sd, *all)),
{
    let first = mark(sd, all, sd, false);
    let marked = mark(sd, all, &first, true);
    upcasts(bases, all, &marked)
}

// ------------------------------------------------------------------ the contract parser

/// A token of a contract line. The shell cuts the text into tokens. `Op` holds `- ` as `Sub`, and the parser reads it as a
/// negation where no operand is before it. `Size` is the text `.size()`, decision 0064. `Field` is `.name`, decision 0073.
/// `HasValue` and `Value` are the texts `.has_value()` and `.value()`, decision 0075. `Empty` is `.empty()`, decision 0078. `Comma`
/// parts the arguments of a call, decision 0079. `Bool` is `true`
/// or `false`, decision 0084. `Old` is the word `old`, decision 0096. `Question` and `Colon` are `?` and `:`, decision 0098.
/// `Cast` is `static_cast<T>` of an integer type `T`, decision 0175.
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
    Real(u64, u32),
    IsFinite,
    Bar,
    Eps,
    Eta,
    DblMax,
    This,
    Cast(Ty),
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

/// The precedence of the contract language, lowest first: `==>`, which groups to the right, then `?:`, then `||`, `&&`, `|`, `&`, a comparison or a
/// chain of two, `+` and `-`, `*`, the prefix `!` and `-`, and the postfix `.size()` and `[e]`. Parentheses group, and `forall j ::`
/// takes all that follows, decision 0064.
/// ponytail: the parser is proved to end and to read each token once, not to follow a grammar written as a spec. Upgrade: the
/// grammar as a spec relation, and a proof that each parse is in it.
fn parse_implies(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 11usize,
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
    decreases toks.len() - pos, 10usize,
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
    decreases toks.len() - pos, 9usize,
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
    decreases toks.len() - pos, 8usize,
{
    let (mut a, mut p) = match parse_bitor(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && toks[p] == Tok::Op(BinOp::And)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_bitor(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::And, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

/// `a | b`, below `&` and above `&&`, as C++ has it, decision 0175. A `|` after a whole operand is this operator. A `|` at the start
/// of an operand opens the absolute value of decision 0154, whose operand stops at the next `|`.
fn parse_bitor(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
    requires
        pos <= toks.len(),
    ensures
        parsed(r, toks@, pos),
    decreases toks.len() - pos, 7usize,
{
    let (mut a, mut p) = match parse_bitand(toks, pos, line) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    while p < toks.len() && toks[p] == Tok::Bar
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_bitand(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::BitOr, Box::new(a), Box::new(b));
                p = q;
            },
            Err(e) => return Err(e),
        }
    }
    Ok((a, p))
}

/// `a & b`, below a comparison, as C++ has it, decision 0175.
fn parse_bitand(toks: &Vec<Tok>, pos: usize, line: u32) -> (r: Result<(Expr, usize), Refusal>)
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
    while p < toks.len() && toks[p] == Tok::Op(BinOp::BitAnd)
        invariant
            pos < p <= toks.len(),
            !unknown_expr(a),
        decreases toks.len() - p,
    {
        match parse_cmp(toks, p + 1, line) {
            Ok((b, q)) => {
                a = Expr::Bin(BinOp::BitAnd, Box::new(a), Box::new(b));
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
            // `o->f` is `o.value().f`, decision 0137. A name of a field follows. `o->f(a)` calls `f` on `o.value()`, decision 0168.
            if toks.len() - p > 1 {
                if let Tok::Ident(f) = toks[p + 1] {
                    let v = Expr::Value(Box::new(a));
                    assert(!unknown_expr(v));
                    if toks.len() - p > 3 && toks[p + 2] == Tok::LParen && toks[p + 3] == Tok::RParen {
                        assert(!unknown_args(List::Nil));
                        a = Expr::MApply(Box::new(v), f, Box::new(List::Nil));
                        p = p + 4;
                    } else if toks.len() - p > 2 && toks[p + 2] == Tok::LParen {
                        match parse_args(toks, p + 3, line) {
                            Ok((args, q)) => {
                                a = Expr::MApply(Box::new(v), f, Box::new(args));
                                p = q;
                            },
                            Err(e) => return Err(e),
                        }
                    } else {
                        a = Expr::Field(Box::new(v), f);
                        p = p + 2;
                    }
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
    decreases toks.len() - pos, 12usize,
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
    decreases toks.len() - pos, 12usize,
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
        Tok::Real(d, k) => Ok((Expr::RealLit(d, k), pos + 1)),
        Tok::Eps => Ok((Expr::Eps, pos + 1)),
        Tok::Eta => Ok((Expr::Eta, pos + 1)),
        Tok::DblMax => Ok((Expr::DblMax, pos + 1)),
        // The operand of `|e|` reads no `|` of its own, so the next `|` closes it.
        Tok::Bar => match parse_bitand(toks, pos + 1, line) {
            Ok((e, p)) => if p < toks.len() && toks[p] == Tok::Bar {
                Ok((Expr::Abs(Box::new(e)), p + 1))
            } else {
                Err(Refusal::Syntax(line))
            },
            Err(e) => Err(e),
        },
        Tok::IsFinite => if toks.len() - pos > 1 && toks[pos + 1] == Tok::LParen {
            match parse_implies(toks, pos + 2, line) {
                Ok((e, p)) => if p < toks.len() && toks[p] == Tok::RParen {
                    Ok((Expr::Finite(Box::new(e)), p + 1))
                } else {
                    Err(Refusal::Syntax(line))
                },
                Err(e) => Err(e),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
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
        // `static_cast<T>(e)`, decision 0175.
        Tok::Cast(t) => if toks.len() - pos > 1 && toks[pos + 1] == Tok::LParen {
            match parse_implies(toks, pos + 2, line) {
                Ok((e, p)) => if p < toks.len() && toks[p] == Tok::RParen {
                    Ok((Expr::StaticCast(t, Box::new(e)), p + 1))
                } else {
                    Err(Refusal::Syntax(line))
                },
                Err(e) => Err(e),
            }
        } else {
            Err(Refusal::Syntax(line))
        },
        // `this->x` reads `x`, and `this->f(a)` calls `f(a)`, decision 0166.
        Tok::This => if toks.len() - pos > 1 && toks[pos + 1] == Tok::Arrow {
            parse_atom(toks, pos + 2, line)
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

// ------------------------------------------------------------------ globals, decision 0173

/// The scalar of a global that can be a reference parameter of 0108. A global of any other type has no rule yet.
pub open spec fn spec_global_scalar(t: Ty) -> Option<Scalar> {
    match t {
        Ty::I32 => Some(Scalar::I32),
        Ty::I64 => Some(Scalar::I64),
        Ty::U8 => Some(Scalar::U8),
        Ty::U32 => Some(Scalar::U32),
        Ty::U64 => Some(Scalar::U64),
        Ty::Bool => Some(Scalar::Bool),
        Ty::Struct(k) => Some(Scalar::Struct(k)),
        _ => None,
    }
}

pub fn global_scalar(t: Ty) -> (r: Option<Scalar>)
    ensures
        r == spec_global_scalar(t),
{
    match t {
        Ty::I32 => Some(Scalar::I32),
        Ty::I64 => Some(Scalar::I64),
        Ty::U8 => Some(Scalar::U8),
        Ty::U32 => Some(Scalar::U32),
        Ty::U64 => Some(Scalar::U64),
        Ty::Bool => Some(Scalar::Bool),
        Ty::Struct(k) => Some(Scalar::Struct(k)),
        _ => None,
    }
}

/// A line of the kind `k` names the global `g`.
pub open spec fn spec_glists(cs: Conds, k: CondKind, g: u32) -> bool
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k2, e, _, _), rest) => (k2 == k && e == Expr::Name(g)) || spec_glists(*rest, k, g),
    }
}

pub fn glists(cs: &Conds, k: CondKind, g: u32) -> (r: bool)
    ensures
        r == spec_glists(*cs, k, g),
    decreases cs,
{
    match cs {
        List::Nil => false,
        List::Cons((k2, e, _, _), rest) => (*k2 == k && match e {
            Expr::Name(n) => *n == g,
            _ => false,
        }) || glists(rest, k, g),
    }
}

/// The line of the first modifies or reads line that names the global `g`.
pub open spec fn spec_gline(cs: Conds, g: u32) -> Option<u32>
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, _), rest) => if (k == CondKind::Modifies || k == CondKind::Reads) && e == Expr::Name(g) {
            Some(l)
        } else {
            spec_gline(*rest, g)
        },
    }
}

pub fn gline(cs: &Conds, g: u32) -> (r: Option<u32>)
    ensures
        r == spec_gline(*cs, g),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, _), rest) => if (*k == CondKind::Modifies || *k == CondKind::Reads) && match e {
            Expr::Name(n) => *n == g,
            _ => false,
        } {
            Some(*l)
        } else {
            gline(rest, g)
        },
    }
}

/// The globals that a function lists, as its implicit parameters, in the order of the globals `gs`. A global on a modifies line is
/// a reference parameter, and one on a reads line only is a parameter by value, decision 0173.
pub open spec fn spec_gparams(cs: Conds, gs: Params) -> Params
    decreases gs,
{
    match gs {
        List::Nil => List::Nil,
        List::Cons((g, t), rest) => if spec_glists(cs, CondKind::Modifies, g) {
            match spec_global_scalar(t) {
                Some(s) => List::Cons((g, Ty::Mut(s)), Box::new(spec_gparams(cs, *rest))),
                None => spec_gparams(cs, *rest),
            }
        } else if spec_glists(cs, CondKind::Reads, g) && spec_global_scalar(t) is Some {
            List::Cons((g, t), Box::new(spec_gparams(cs, *rest)))
        } else {
            spec_gparams(cs, *rest)
        },
    }
}

pub fn gparams(cs: &Conds, gs: &Params) -> (r: Params)
    ensures
        r == spec_gparams(*cs, *gs),
    decreases gs,
{
    match gs {
        List::Nil => List::Nil,
        List::Cons((g, t), rest) => if glists(cs, CondKind::Modifies, *g) {
            match global_scalar(*t) {
                Some(s) => List::Cons((*g, Ty::Mut(s)), Box::new(gparams(cs, rest))),
                None => gparams(cs, rest),
            }
        } else if glists(cs, CondKind::Reads, *g) && global_scalar(*t).is_some() {
            List::Cons((*g, *t), Box::new(gparams(cs, rest)))
        } else {
            gparams(cs, rest)
        },
    }
}

/// A use of the name `v` of type `t`. A name that a parameter, a local or a parameter of a lambda hides stays. A global that the
/// function lists has the type of its implicit parameter. A global that the function does not list names nothing, so it is refused
/// as a name. Any other name stays.
pub open spec fn spec_gvar(v: u32, t: Ty, gs: Params, gps: Params, hide: Names) -> Expr {
    if spec_has(hide, v) {
        Expr::Var(v, t)
    } else {
        match spec_get(gps, v) {
            Some(t2) => Expr::Var(v, t2),
            None => if spec_get(gs, v) is Some {
                Expr::Name(v)
            } else {
                Expr::Var(v, t)
            },
        }
    }
}

pub fn gvar(v: u32, t: Ty, gs: &Params, gps: &Params, hide: &Names) -> (r: Expr)
    ensures
        r == spec_gvar(v, t, *gs, *gps, *hide),
{
    if has(hide, v) {
        Expr::Var(v, t)
    } else {
        match get(gps, v) {
            Some(t2) => Expr::Var(v, t2),
            None => if get(gs, v).is_some() {
                Expr::Name(v)
            } else {
                Expr::Var(v, t)
            },
        }
    }
}

/// The arguments that a call adds for the globals `cps` of its callee: the parameter of the caller of each name, or the name alone,
/// which is refused, when the caller lists no such global.
pub open spec fn spec_gpass(cps: Params, gps: Params) -> Args
    decreases cps,
{
    match cps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(Box::new(match spec_get(gps, g) {
            Some(t2) => Expr::Var(g, t2),
            None => Expr::Name(g),
        }), Box::new(spec_gpass(*rest, gps))),
    }
}

pub fn gpass(cps: &Params, gps: &Params) -> (r: Args)
    ensures
        r == spec_gpass(*cps, *gps),
    decreases cps,
{
    match cps {
        List::Nil => List::Nil,
        List::Cons((g, _), rest) => List::Cons(Box::new(match get(gps, *g) {
            Some(t2) => Expr::Var(*g, t2),
            None => Expr::Name(*g),
        }), Box::new(gpass(rest, gps))),
    }
}

/// The arguments of the globals of the callee `k`.
pub open spec fn spec_gextra(k: u32, gs: Params, gps: Params, fs: Fns) -> Args {
    match spec_find(fs, k) {
        Some(cf) => spec_gpass(spec_gparams(cf.conds, gs), gps),
        None => List::Nil,
    }
}

pub fn gextra(k: u32, gs: &Params, gps: &Params, fs: &Fns) -> (r: Args)
    ensures
        r == spec_gextra(k, *gs, *gps, *fs),
{
    match find(fs, k) {
        Some(cf) => gpass(&gparams(&cf.conds, gs), gps),
        None => List::Nil,
    }
}

/// An expression of code with each global typed by the implicit parameters `gps`, and each call given the globals of its callee.
pub open spec fn spec_gexpr(e: Expr, gs: Params, gps: Params, hide: Names, fs: Fns) -> Expr
    decreases e,
{
    match e {
        Expr::Int(f0) => Expr::Int(f0),
        Expr::Lit(f0, f1) => Expr::Lit(f0, f1),
        Expr::Bool(f0) => Expr::Bool(f0),
        Expr::Var(v, t) => spec_gvar(v, t, gs, gps, hide),
        Expr::Name(f0) => Expr::Name(f0),
        Expr::Result => Expr::Result,
        Expr::Bin(f0, f1, f2) => Expr::Bin(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Not(f0) => Expr::Not(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Neg(f0) => Expr::Neg(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Cast(f0, f1) => Expr::Cast(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Paren(f0) => Expr::Paren(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Brace(f0) => Expr::Brace(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Call(k, nm, args, at) => Expr::Call(k, nm, Box::new(spec_append(spec_gargs(*args, gs, gps, hide, fs), spec_gextra(k, gs, gps, fs))), at),
        Expr::Size(f0) => Expr::Size(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Index(f0, f1) => Expr::Index(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Copy(f0, f1, f2) => Expr::Copy(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, f2),
        Expr::Field(f0, f1) => Expr::Field(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1),
        Expr::Construct(f0, f1) => Expr::Construct(f0, Box::new(spec_gargs(*f1, gs, gps, hide, fs))),
        Expr::Forall(f0, f1) => Expr::Forall(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Exists(f0, f1) => Expr::Exists(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Chain(f0, f1, f2, f3, f4) => Expr::Chain(f0, f1, Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), Box::new(spec_gexpr(*f3, gs, gps, hide, fs)), Box::new(spec_gexpr(*f4, gs, gps, hide, fs))),
        Expr::HasValue(f0) => Expr::HasValue(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Value(f0) => Expr::Value(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Nullopt => Expr::Nullopt,
        Expr::Wrap(f0) => Expr::Wrap(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Empty(f0) => Expr::Empty(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Subspan(f0, f1) => Expr::Subspan(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Apply(f0, f1) => Expr::Apply(f0, Box::new(spec_gargs(*f1, gs, gps, hide, fs))),
        Expr::Suffix(f0, f1) => Expr::Suffix(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Prefix(f0, f1) => Expr::Prefix(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Slice(f0, f1, f2) => Expr::Slice(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Divide(f0, f1, f2, f3) => Expr::Divide(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), f3),
        Expr::MApply(f0, f1, f2) => Expr::MApply(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, Box::new(spec_gargs(*f2, gs, gps, hide, fs))),
        Expr::Old(f0) => Expr::Old(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Cond(f0, f1, f2) => Expr::Cond(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs))),
        Expr::Shr(f0, f1, f2) => Expr::Shr(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), f2),
        Expr::Bits(f0, f1, f2, f3) => Expr::Bits(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs)), Box::new(spec_gexpr(*f2, gs, gps, hide, fs)), f3),
        Expr::StaticCast(f0, f1) => Expr::StaticCast(f0, Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::List(f0) => Expr::List(Box::new(spec_gargs(*f0, gs, gps, hide, fs))),
        // A write of a global writes the parameter that it becomes, decision 0177.
        Expr::Step(f0, f1, f2, f3) => match spec_gvar(f0, f1, gs, gps, hide) {
            Expr::Var(v, t) => Expr::Step(v, t, f2, f3),
            other => other,
        },
        Expr::Enumerator(f0, f1) => Expr::Enumerator(f0, f1),
        // The parameter of the lambda hides a global of its name in the body, as in C++.
        Expr::CountIf(f0, f1, f2, f3) => Expr::CountIf(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), f1, f2, Box::new(spec_gexpr(*f3, gs, gps, List::Cons(f1, Box::new(hide)), fs))),
        Expr::RealLit(f0, f1) => Expr::RealLit(f0, f1),
        Expr::Ratio(f0, f1) => Expr::Ratio(f0, f1),
        Expr::Finite(f0) => Expr::Finite(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Abs(f0) => Expr::Abs(Box::new(spec_gexpr(*f0, gs, gps, hide, fs))),
        Expr::Eps => Expr::Eps,
        Expr::Eta => Expr::Eta,
        Expr::DblMax => Expr::DblMax,
        Expr::EmptyVec => Expr::EmptyVec,
        Expr::Fill(f0, f1) => Expr::Fill(Box::new(spec_gexpr(*f0, gs, gps, hide, fs)), Box::new(spec_gexpr(*f1, gs, gps, hide, fs))),
        Expr::Move(f0, f1) => Expr::Move(f0, f1),
        Expr::Unknown(f0, f1) => Expr::Unknown(f0, f1),
    }
}

pub open spec fn spec_gargs(args: Args, gs: Params, gps: Params, hide: Names, fs: Fns) -> Args
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => List::Cons(Box::new(spec_gexpr(*a, gs, gps, hide, fs)), Box::new(spec_gargs(*rest, gs, gps, hide, fs))),
    }
}

pub fn gexpr(e: &Expr, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Expr)
    ensures
        r == spec_gexpr(*e, *gs, *gps, *hide, *fs),
    decreases e,
{
    match e {
        Expr::Int(f0) => Expr::Int(*f0),
        Expr::Lit(f0, f1) => Expr::Lit(*f0, *f1),
        Expr::Bool(f0) => Expr::Bool(*f0),
        Expr::Var(v, t) => gvar(*v, *t, gs, gps, hide),
        Expr::Name(f0) => Expr::Name(*f0),
        Expr::Result => Expr::Result,
        Expr::Bin(f0, f1, f2) => Expr::Bin(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Not(f0) => Expr::Not(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Neg(f0) => Expr::Neg(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Cast(f0, f1) => Expr::Cast(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Paren(f0) => Expr::Paren(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Brace(f0) => Expr::Brace(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Call(k, nm, args, at) => Expr::Call(*k, *nm, Box::new(append(gargs(args, gs, gps, hide, fs), gextra(*k, gs, gps, fs))), *at),
        Expr::Size(f0) => Expr::Size(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Index(f0, f1) => Expr::Index(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Copy(f0, f1, f2) => Expr::Copy(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, *f2),
        Expr::Field(f0, f1) => Expr::Field(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1),
        Expr::Construct(f0, f1) => Expr::Construct(*f0, Box::new(gargs(f1, gs, gps, hide, fs))),
        Expr::Forall(f0, f1) => Expr::Forall(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Exists(f0, f1) => Expr::Exists(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Chain(f0, f1, f2, f3, f4) => Expr::Chain(*f0, *f1, Box::new(gexpr(f2, gs, gps, hide, fs)), Box::new(gexpr(f3, gs, gps, hide, fs)), Box::new(gexpr(f4, gs, gps, hide, fs))),
        Expr::HasValue(f0) => Expr::HasValue(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Value(f0) => Expr::Value(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Nullopt => Expr::Nullopt,
        Expr::Wrap(f0) => Expr::Wrap(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Empty(f0) => Expr::Empty(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Subspan(f0, f1) => Expr::Subspan(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Apply(f0, f1) => Expr::Apply(*f0, Box::new(gargs(f1, gs, gps, hide, fs))),
        Expr::Suffix(f0, f1) => Expr::Suffix(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Prefix(f0, f1) => Expr::Prefix(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Slice(f0, f1, f2) => Expr::Slice(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Divide(f0, f1, f2, f3) => Expr::Divide(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs)), *f3),
        Expr::MApply(f0, f1, f2) => Expr::MApply(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, Box::new(gargs(f2, gs, gps, hide, fs))),
        Expr::Old(f0) => Expr::Old(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Cond(f0, f1, f2) => Expr::Cond(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs))),
        Expr::Shr(f0, f1, f2) => Expr::Shr(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs)), *f2),
        Expr::Bits(f0, f1, f2, f3) => Expr::Bits(*f0, Box::new(gexpr(f1, gs, gps, hide, fs)), Box::new(gexpr(f2, gs, gps, hide, fs)), *f3),
        Expr::StaticCast(f0, f1) => Expr::StaticCast(*f0, Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::List(f0) => Expr::List(Box::new(gargs(f0, gs, gps, hide, fs))),
        Expr::Step(f0, f1, f2, f3) => match gvar(*f0, *f1, gs, gps, hide) {
            Expr::Var(v, t) => Expr::Step(v, t, *f2, *f3),
            other => other,
        },
        Expr::Enumerator(f0, f1) => Expr::Enumerator(*f0, *f1),
        Expr::CountIf(f0, f1, f2, f3) => Expr::CountIf(Box::new(gexpr(f0, gs, gps, hide, fs)), *f1, *f2, Box::new(gexpr(f3, gs, gps, &List::Cons(*f1, Box::new(copy(hide))), fs))),
        Expr::RealLit(f0, f1) => Expr::RealLit(*f0, *f1),
        Expr::Ratio(f0, f1) => Expr::Ratio(*f0, *f1),
        Expr::Finite(f0) => Expr::Finite(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Abs(f0) => Expr::Abs(Box::new(gexpr(f0, gs, gps, hide, fs))),
        Expr::Eps => Expr::Eps,
        Expr::Eta => Expr::Eta,
        Expr::DblMax => Expr::DblMax,
        Expr::EmptyVec => Expr::EmptyVec,
        Expr::Fill(f0, f1) => Expr::Fill(Box::new(gexpr(f0, gs, gps, hide, fs)), Box::new(gexpr(f1, gs, gps, hide, fs))),
        Expr::Move(f0, f1) => Expr::Move(*f0, *f1),
        Expr::Unknown(f0, f1) => Expr::Unknown(*f0, *f1),
    }
}

pub fn gargs(args: &Args, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Args)
    ensures
        r == spec_gargs(*args, *gs, *gps, *hide, *fs),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => List::Cons(Box::new(gexpr(a, gs, gps, hide, fs)), Box::new(gargs(rest, gs, gps, hide, fs))),
    }
}

/// The calls of an expression, as the key, the id of the name and the line of each.
pub open spec fn spec_gcalls(e: Expr) -> List<(u32, u32, u32)>
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::Not(f0) => spec_gcalls(*f0),
        Expr::Neg(f0) => spec_gcalls(*f0),
        Expr::Cast(_, f1) => spec_gcalls(*f1),
        Expr::Paren(f0) => spec_gcalls(*f0),
        Expr::Brace(f0) => spec_gcalls(*f0),
        Expr::Call(k, nm, args, at) => List::Cons((k, nm, at), Box::new(spec_gcalls_args(*args))),
        Expr::Size(f0) => spec_gcalls(*f0),
        Expr::Index(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Copy(f0, _, _) => spec_gcalls(*f0),
        Expr::Field(f0, _) => spec_gcalls(*f0),
        Expr::Construct(_, f1) => spec_gcalls_args(*f1),
        Expr::Forall(_, f1) => spec_gcalls(*f1),
        Expr::Exists(_, f1) => spec_gcalls(*f1),
        Expr::Chain(_, _, f2, f3, f4) => spec_append(spec_gcalls(*f2), spec_append(spec_gcalls(*f3), spec_gcalls(*f4))),
        Expr::HasValue(f0) => spec_gcalls(*f0),
        Expr::Value(f0) => spec_gcalls(*f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => spec_gcalls(*f0),
        Expr::Empty(f0) => spec_gcalls(*f0),
        Expr::Subspan(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Apply(_, f1) => spec_gcalls_args(*f1),
        Expr::Suffix(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Prefix(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Slice(f0, f1, f2) => spec_append(spec_gcalls(*f0), spec_append(spec_gcalls(*f1), spec_gcalls(*f2))),
        Expr::Divide(_, f1, f2, _) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::MApply(f0, _, f2) => spec_append(spec_gcalls(*f0), spec_gcalls_args(*f2)),
        Expr::Old(f0) => spec_gcalls(*f0),
        Expr::Cond(f0, f1, f2) => spec_append(spec_gcalls(*f0), spec_append(spec_gcalls(*f1), spec_gcalls(*f2))),
        Expr::Shr(f0, f1, _) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Bits(_, f1, f2, _) => spec_append(spec_gcalls(*f1), spec_gcalls(*f2)),
        Expr::StaticCast(_, f1) => spec_gcalls(*f1),
        Expr::List(f0) => spec_gcalls_args(*f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => spec_append(spec_gcalls(*f0), spec_gcalls(*f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => spec_gcalls(*f0),
        Expr::Abs(f0) => spec_gcalls(*f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => spec_append(spec_gcalls(*f0), spec_gcalls(*f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub open spec fn spec_gcalls_args(args: Args) -> List<(u32, u32, u32)>
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_gcalls(*a), spec_gcalls_args(*rest)),
    }
}

pub fn gcalls(e: &Expr) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls(*e),
    decreases e,
{
    match e {
        Expr::Int(_) => List::Nil,
        Expr::Lit(_, _) => List::Nil,
        Expr::Bool(_) => List::Nil,
        Expr::Var(_, _) => List::Nil,
        Expr::Name(_) => List::Nil,
        Expr::Result => List::Nil,
        Expr::Bin(_, f1, f2) => append(gcalls(f1), gcalls(f2)),
        Expr::Not(f0) => gcalls(f0),
        Expr::Neg(f0) => gcalls(f0),
        Expr::Cast(_, f1) => gcalls(f1),
        Expr::Paren(f0) => gcalls(f0),
        Expr::Brace(f0) => gcalls(f0),
        Expr::Call(k, nm, args, at) => List::Cons((*k, *nm, *at), Box::new(gcalls_args(args))),
        Expr::Size(f0) => gcalls(f0),
        Expr::Index(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Copy(f0, _, _) => gcalls(f0),
        Expr::Field(f0, _) => gcalls(f0),
        Expr::Construct(_, f1) => gcalls_args(f1),
        Expr::Forall(_, f1) => gcalls(f1),
        Expr::Exists(_, f1) => gcalls(f1),
        Expr::Chain(_, _, f2, f3, f4) => append(gcalls(f2), append(gcalls(f3), gcalls(f4))),
        Expr::HasValue(f0) => gcalls(f0),
        Expr::Value(f0) => gcalls(f0),
        Expr::Nullopt => List::Nil,
        Expr::Wrap(f0) => gcalls(f0),
        Expr::Empty(f0) => gcalls(f0),
        Expr::Subspan(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Apply(_, f1) => gcalls_args(f1),
        Expr::Suffix(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Prefix(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Slice(f0, f1, f2) => append(gcalls(f0), append(gcalls(f1), gcalls(f2))),
        Expr::Divide(_, f1, f2, _) => append(gcalls(f1), gcalls(f2)),
        Expr::MApply(f0, _, f2) => append(gcalls(f0), gcalls_args(f2)),
        Expr::Old(f0) => gcalls(f0),
        Expr::Cond(f0, f1, f2) => append(gcalls(f0), append(gcalls(f1), gcalls(f2))),
        Expr::Shr(f0, f1, _) => append(gcalls(f0), gcalls(f1)),
        Expr::Bits(_, f1, f2, _) => append(gcalls(f1), gcalls(f2)),
        Expr::StaticCast(_, f1) => gcalls(f1),
        Expr::List(f0) => gcalls_args(f0),
        Expr::Step(_, _, _, _) => List::Nil,
        Expr::Enumerator(_, _) => List::Nil,
        Expr::CountIf(f0, _, _, f3) => append(gcalls(f0), gcalls(f3)),
        Expr::RealLit(_, _) => List::Nil,
        Expr::Ratio(_, _) => List::Nil,
        Expr::Finite(f0) => gcalls(f0),
        Expr::Abs(f0) => gcalls(f0),
        Expr::Eps => List::Nil,
        Expr::Eta => List::Nil,
        Expr::DblMax => List::Nil,
        Expr::EmptyVec => List::Nil,
        Expr::Fill(f0, f1) => append(gcalls(f0), gcalls(f1)),
        Expr::Move(_, _) => List::Nil,
        Expr::Unknown(_, _) => List::Nil,
    }
}

pub fn gcalls_args(args: &Args) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(gcalls(a), gcalls_args(rest)),
    }
}

/// A write to the name `n` that is a global the function neither lists nor hides. It names nothing, so the pass refuses the name.
pub open spec fn spec_gwrite_bad(n: u32, gs: Params, gps: Params, hide: Names) -> bool {
    spec_get(gps, n) is None && spec_get(gs, n) is Some && !spec_has(hide, n)
}

pub fn gwrite_bad(n: u32, gs: &Params, gps: &Params, hide: &Names) -> (r: bool)
    ensures
        r == spec_gwrite_bad(n, *gs, *gps, *hide),
{
    get(gps, n).is_none() && get(gs, n).is_some() && !(has(hide, n))
}

/// A statement of the body with each global typed by the implicit parameters and each call given the globals of its callee. The
/// lines of a loop and the lines of an assert or apply are contract lines, which read a global by its name, so they stay.
pub open spec fn spec_gstmt(s: Stmt, gs: Params, gps: Params, hide: Names, fs: Fns) -> Stmt
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::If(c, t, f, l) => Stmt::If(spec_gexpr(c, gs, gps, hide, fs), Box::new(spec_gstmts(*t, gs, gps, hide, fs)), Box::new(spec_gstmts(*f, gs, gps, hide, fs)), l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(spec_gstmts(*b, gs, gps, hide, fs)), l),
        Stmt::Local(n, t, e, l) => Stmt::Local(n, t, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::Assign(n, e, l) => if spec_gwrite_bad(n, gs, gps, hide) {
            Stmt::Assign(n, Expr::Name(n), l)
        } else {
            Stmt::Assign(n, spec_gexpr(e, gs, gps, hide, fs), l)
        },
        Stmt::Step(n, t, up, l) => if spec_gwrite_bad(n, gs, gps, hide) {
            Stmt::Assign(n, Expr::Name(n), l)
        } else {
            Stmt::Step(n, t, up, l)
        },
        Stmt::While(c, lc, body, l) => Stmt::While(spec_gexpr(c, gs, gps, hide, fs), lc, Box::new(spec_gstmts(*body, gs, gps, hide, fs)), l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(spec_gstmt(*init, gs, gps, hide, fs)),
            spec_gexpr(c, gs, gps, hide, fs),
            Box::new(spec_gstmt(*step, gs, gps, hide, fs)),
            lc,
            Box::new(spec_gstmts(*body, gs, gps, hide, fs)),
            l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(x, f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(x, f, spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(spec_gexpr(e, gs, gps, hide, fs), k, Box::new(spec_gcases(*cs, gs, gps, hide, fs)), l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(k, nm, Box::new(spec_append(spec_gargs(*args, gs, gps, hide, fs), spec_gextra(k, gs, gps, fs))), l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(fr, x, xt, spec_gexpr(sq, gs, gps, hide, fs), lc, Box::new(spec_gstmts(*body, gs, gps, hide, fs)), l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(v, spec_gexpr(i, gs, gps, hide, fs), spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(f, spec_gexpr(i, gs, gps, hide, fs), spec_gexpr(e, gs, gps, hide, fs), l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(v, spec_gexpr(e, gs, gps, hide, fs), l),
        // The comparator reads a listed global as the function does. Its two parameters hide globals of their names.
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(v, a, b, t, spec_gexpr(e, gs, gps, List::Cons(a, Box::new(List::Cons(b, Box::new(hide)))), fs), l),
        _ => s,
    }
}

pub open spec fn spec_gstmts(ss: Stmts, gs: Params, gps: Params, hide: Names, fs: Fns) -> Stmts
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(spec_gstmt(*s, gs, gps, hide, fs)), Box::new(spec_gstmts(*rest, gs, gps, hide, fs))),
    }
}

pub open spec fn spec_gcases(cs: Cases, gs: Params, gps: Params, hide: Names, fs: Fns) -> Cases
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((i, Box::new(spec_gstmts(*body, gs, gps, hide, fs))), Box::new(spec_gcases(*rest, gs, gps, hide, fs))),
    }
}

pub fn copy_conds(cs: &Conds) -> (r: Conds)
    ensures
        r == *cs,
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, d), rest) => List::Cons((*k, copy_expr(e), *l, copy(d)), Box::new(copy_conds(rest))),
    }
}

pub fn copy_stmt(s: &Stmt) -> (r: Stmt)
    ensures
        r == *s,
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(copy_expr(e), *l),
        Stmt::If(c, t, f, l) => Stmt::If(copy_expr(c), Box::new(copy_stmts(t)), Box::new(copy_stmts(f)), *l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(copy_stmts(b)), *l),
        Stmt::Local(n, t, e, l) => Stmt::Local(*n, *t, copy_expr(e), *l),
        Stmt::Assign(n, e, l) => Stmt::Assign(*n, copy_expr(e), *l),
        Stmt::Step(n, t, up, l) => Stmt::Step(*n, *t, *up, *l),
        Stmt::While(c, lc, body, l) => Stmt::While(copy_expr(c), Box::new(copy_conds(lc)), Box::new(copy_stmts(body)), *l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(copy_stmt(init)),
            copy_expr(c),
            Box::new(copy_stmt(step)),
            Box::new(copy_conds(lc)),
            Box::new(copy_stmts(body)),
            *l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(*f, copy_expr(e), *l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(*x, *f, copy_expr(e), *l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(*x, *f, copy_expr(e), *l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(copy_expr(e), *k, Box::new(copy_cases(cs)), *l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(*k, *nm, Box::new(copy_args(args)), *l),
        Stmt::Exit(l) => Stmt::Exit(*l),
        Stmt::Assert(e, l) => Stmt::Assert(copy_expr(e), *l),
        Stmt::Apply(k, args, l) => Stmt::Apply(*k, Box::new(copy_args(args)), *l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(*fr, *x, *xt, copy_expr(sq), Box::new(copy_conds(lc)), Box::new(copy_stmts(body)), *l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(*v, copy_expr(i), copy_expr(e), *l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(*f, copy_expr(i), copy_expr(e), *l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(*v, copy_expr(e), *l),
        Stmt::Sort(v, l) => Stmt::Sort(*v, *l),
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(*v, *a, *b, *t, copy_expr(e), *l),
        Stmt::Unknown(k, l) => Stmt::Unknown(*k, *l),
    }
}

pub fn copy_stmts(ss: &Stmts) -> (r: Stmts)
    ensures
        r == *ss,
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(copy_stmt(s)), Box::new(copy_stmts(rest))),
    }
}

pub fn copy_cases(cs: &Cases) -> (r: Cases)
    ensures
        r == *cs,
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((*i, Box::new(copy_stmts(body))), Box::new(copy_cases(rest))),
    }
}

pub fn gstmt(s: &Stmt, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Stmt)
    ensures
        r == spec_gstmt(*s, *gs, *gps, *hide, *fs),
    decreases s,
{
    match s {
        Stmt::Return(e, l) => Stmt::Return(gexpr(e, gs, gps, hide, fs), *l),
        Stmt::If(c, t, f, l) => Stmt::If(gexpr(c, gs, gps, hide, fs), Box::new(gstmts(t, gs, gps, hide, fs)), Box::new(gstmts(f, gs, gps, hide, fs)), *l),
        Stmt::Block(b, l) => Stmt::Block(Box::new(gstmts(b, gs, gps, hide, fs)), *l),
        Stmt::Local(n, t, e, l) => Stmt::Local(*n, *t, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::Assign(n, e, l) => if gwrite_bad(*n, gs, gps, hide) {
            Stmt::Assign(*n, Expr::Name(*n), *l)
        } else {
            Stmt::Assign(*n, gexpr(e, gs, gps, hide, fs), *l)
        },
        Stmt::Step(n, t, up, l) => if gwrite_bad(*n, gs, gps, hide) {
            Stmt::Assign(*n, Expr::Name(*n), *l)
        } else {
            Stmt::Step(*n, *t, *up, *l)
        },
        Stmt::While(c, lc, body, l) => Stmt::While(gexpr(c, gs, gps, hide, fs), Box::new(copy_conds(lc)), Box::new(gstmts(body, gs, gps, hide, fs)), *l),
        Stmt::For(init, c, step, lc, body, l) => Stmt::For(
            Box::new(gstmt(init, gs, gps, hide, fs)),
            gexpr(c, gs, gps, hide, fs),
            Box::new(gstmt(step, gs, gps, hide, fs)),
            Box::new(copy_conds(lc)),
            Box::new(gstmts(body, gs, gps, hide, fs)),
            *l,
        ),
        Stmt::SetField(f, e, l) => Stmt::SetField(*f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetRefField(x, f, e, l) => Stmt::SetRefField(*x, *f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetOwnField(x, f, e, l) => Stmt::SetOwnField(*x, *f, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::Switch(e, k, cs, l) => Stmt::Switch(gexpr(e, gs, gps, hide, fs), *k, Box::new(gcases(cs, gs, gps, hide, fs)), *l),
        Stmt::Call(k, nm, args, l) => Stmt::Call(*k, *nm, Box::new(append(gargs(args, gs, gps, hide, fs), gextra(*k, gs, gps, fs))), *l),
        Stmt::RangeFor(fr, x, xt, sq, lc, body, l) => Stmt::RangeFor(*fr, *x, *xt, gexpr(sq, gs, gps, hide, fs), Box::new(copy_conds(lc)), Box::new(gstmts(body, gs, gps, hide, fs)), *l),
        Stmt::SetIndex(v, i, e, l) => Stmt::SetIndex(*v, gexpr(i, gs, gps, hide, fs), gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SetFieldAt(f, i, e, l) => Stmt::SetFieldAt(*f, gexpr(i, gs, gps, hide, fs), gexpr(e, gs, gps, hide, fs), *l),
        Stmt::PushBack(v, e, l) => Stmt::PushBack(*v, gexpr(e, gs, gps, hide, fs), *l),
        Stmt::SortBy(v, a, b, t, e, l) => Stmt::SortBy(*v, *a, *b, *t, gexpr(e, gs, gps, &List::Cons(*a, Box::new(List::Cons(*b, Box::new(copy(hide))))), fs), *l),
        _ => copy_stmt(s),
    }
}

pub fn gstmts(ss: &Stmts, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Stmts)
    ensures
        r == spec_gstmts(*ss, *gs, *gps, *hide, *fs),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(Box::new(gstmt(s, gs, gps, hide, fs)), Box::new(gstmts(rest, gs, gps, hide, fs))),
    }
}

pub fn gcases(cs: &Cases, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Cases)
    ensures
        r == spec_gcases(*cs, *gs, *gps, *hide, *fs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((i, body), rest) => List::Cons((*i, Box::new(gstmts(body, gs, gps, hide, fs))), Box::new(gcases(rest, gs, gps, hide, fs))),
    }
}

/// The names of the locals of a body, at any depth, and the indexes and elements of its range-fors.
pub open spec fn spec_glocals(ss: Stmts) -> Names
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_glocals_stmt(*s), spec_glocals(*rest)),
    }
}

pub open spec fn spec_glocals_stmt(s: Stmt) -> Names
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, _) => List::Cons(n, Box::new(List::Nil)),
        Stmt::If(_, t, f, _) => spec_append(spec_glocals(*t), spec_glocals(*f)),
        Stmt::While(_, _, body, _) => spec_glocals(*body),
        Stmt::For(init, _, step, _, body, _) => spec_append(spec_glocals_stmt(*init), spec_append(spec_glocals_stmt(*step), spec_glocals(*body))),
        Stmt::Switch(_, _, cs, _) => spec_glocals_cases(*cs),
        Stmt::RangeFor(fr, x, _, _, _, body, _) => List::Cons(fr, Box::new(List::Cons(x, Box::new(spec_glocals(*body))))),
        _ => List::Nil,
    }
}

pub open spec fn spec_glocals_cases(cs: Cases) -> Names
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_glocals(*body), spec_glocals_cases(*rest)),
    }
}

pub fn glocals(ss: &Stmts) -> (r: Names)
    ensures
        r == spec_glocals(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(glocals_stmt(s), glocals(rest)),
    }
}

pub fn glocals_stmt(s: &Stmt) -> (r: Names)
    ensures
        r == spec_glocals_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Local(n, _, _, _) => List::Cons(*n, Box::new(List::Nil)),
        Stmt::If(_, t, f, _) => append(glocals(t), glocals(f)),
        Stmt::While(_, _, body, _) => glocals(body),
        Stmt::For(init, _, step, _, body, _) => append(glocals_stmt(init), append(glocals_stmt(step), glocals(body))),
        Stmt::Switch(_, _, cs, _) => glocals_cases(cs),
        Stmt::RangeFor(fr, x, _, _, _, body, _) => List::Cons(*fr, Box::new(List::Cons(*x, Box::new(glocals(body))))),
        _ => List::Nil,
    }
}

pub fn glocals_cases(cs: &Cases) -> (r: Names)
    ensures
        r == spec_glocals_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(glocals(body), glocals_cases(rest)),
    }
}

/// The calls of a body, at any depth, as the key, the id of the name and the line of each.
pub open spec fn spec_gcalls_stmts(ss: Stmts) -> List<(u32, u32, u32)>
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => spec_append(spec_gcalls_stmt(*s), spec_gcalls_stmts(*rest)),
    }
}

pub open spec fn spec_gcalls_stmt(s: Stmt) -> List<(u32, u32, u32)>
    decreases s,
{
    match s {
        Stmt::Return(e, _) => spec_gcalls(e),
        Stmt::If(c, t, f, _) => spec_append(spec_gcalls(c), spec_append(spec_gcalls_stmts(*t), spec_gcalls_stmts(*f))),
        Stmt::Local(_, _, e, _) => spec_gcalls(e),
        Stmt::Assign(_, e, _) => spec_gcalls(e),
        Stmt::While(c, _, body, _) => spec_append(spec_gcalls(c), spec_gcalls_stmts(*body)),
        Stmt::For(init, c, step, _, body, _) => spec_append(spec_gcalls_stmt(*init), spec_append(spec_gcalls(c), spec_append(spec_gcalls_stmt(*step), spec_gcalls_stmts(*body)))),
        Stmt::SetField(_, e, _) => spec_gcalls(e),
        Stmt::SetRefField(_, _, e, _) => spec_gcalls(e),
        Stmt::SetOwnField(_, _, e, _) => spec_gcalls(e),
        Stmt::Switch(e, _, cs, _) => spec_append(spec_gcalls(e), spec_gcalls_cases(*cs)),
        Stmt::Call(k, nm, args, l) => List::Cons((k, nm, l), Box::new(spec_gcalls_args(*args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => spec_append(spec_gcalls(sq), spec_gcalls_stmts(*body)),
        Stmt::SetIndex(_, i, e, _) => spec_append(spec_gcalls(i), spec_gcalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => spec_append(spec_gcalls(i), spec_gcalls(e)),
        Stmt::PushBack(_, e, _) => spec_gcalls(e),
        _ => List::Nil,
    }
}

pub open spec fn spec_gcalls_cases(cs: Cases) -> List<(u32, u32, u32)>
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => spec_append(spec_gcalls_stmts(*body), spec_gcalls_cases(*rest)),
    }
}

pub fn gcalls_stmts(ss: &Stmts) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_stmts(*ss),
    decreases ss,
{
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => append(gcalls_stmt(s), gcalls_stmts(rest)),
    }
}

pub fn gcalls_stmt(s: &Stmt) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_stmt(*s),
    decreases s,
{
    match s {
        Stmt::Return(e, _) => gcalls(e),
        Stmt::If(c, t, f, _) => append(gcalls(c), append(gcalls_stmts(t), gcalls_stmts(f))),
        Stmt::Local(_, _, e, _) => gcalls(e),
        Stmt::Assign(_, e, _) => gcalls(e),
        Stmt::While(c, _, body, _) => append(gcalls(c), gcalls_stmts(body)),
        Stmt::For(init, c, step, _, body, _) => append(gcalls_stmt(init), append(gcalls(c), append(gcalls_stmt(step), gcalls_stmts(body)))),
        Stmt::SetField(_, e, _) => gcalls(e),
        Stmt::SetRefField(_, _, e, _) => gcalls(e),
        Stmt::SetOwnField(_, _, e, _) => gcalls(e),
        Stmt::Switch(e, _, cs, _) => append(gcalls(e), gcalls_cases(cs)),
        Stmt::Call(k, nm, args, l) => List::Cons((*k, *nm, *l), Box::new(gcalls_args(args))),
        Stmt::RangeFor(_, _, _, sq, _, body, _) => append(gcalls(sq), gcalls_stmts(body)),
        Stmt::SetIndex(_, i, e, _) => append(gcalls(i), gcalls(e)),
        Stmt::SetFieldAt(_, i, e, _) => append(gcalls(i), gcalls(e)),
        Stmt::PushBack(_, e, _) => gcalls(e),
        _ => List::Nil,
    }
}

pub fn gcalls_cases(cs: &Cases) -> (r: List<(u32, u32, u32)>)
    ensures
        r == spec_gcalls_cases(*cs),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((_, body), rest) => append(gcalls_stmts(body), gcalls_cases(rest)),
    }
}

/// The first global among `todo` that a line lists and that has a type with no rule, decision 0173.
pub open spec fn spec_gtype_bad(cs: Conds, todo: Params) -> Option<Refusal>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, t), rest) => match spec_gline(cs, g) {
            Some(l) => if spec_global_scalar(t) is None {
                Some(Refusal::GlobalType(l))
            } else {
                spec_gtype_bad(cs, *rest)
            },
            None => spec_gtype_bad(cs, *rest),
        },
    }
}

pub fn gtype_bad(cs: &Conds, todo: &Params) -> (r: Option<Refusal>)
    ensures
        r == spec_gtype_bad(*cs, *todo),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, t), rest) => match gline(cs, *g) {
            Some(l) => if global_scalar(*t).is_none() {
                Some(Refusal::GlobalType(l))
            } else {
                gtype_bad(cs, rest)
            },
            None => gtype_bad(cs, rest),
        },
    }
}

/// The line of the first line that lists a global among `todo`.
pub open spec fn spec_glisted(cs: Conds, todo: Params) -> Option<u32>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => match spec_gline(cs, g) {
            Some(l) => Some(l),
            None => spec_glisted(cs, *rest),
        },
    }
}

pub fn glisted(cs: &Conds, todo: &Params) -> (r: Option<u32>)
    ensures
        r == spec_glisted(*cs, *todo),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => match gline(cs, *g) {
            Some(l) => Some(l),
            None => glisted(cs, rest),
        },
    }
}

/// A member function: its first parameter is an object, or it is a constructor.
/// A member that cannot list a global yet: a `const` member function, whose function twin would take no global, or a virtual
/// function. A member that writes its object, a constructor and a destructor can list one, decision 0178.
pub open spec fn spec_gmember(f: Function) -> bool {
    match spec_head_ty(f.params) {
        Some(t) => t is This || t is Iface || t is IfaceMut,
        None => false,
    }
}

pub fn gmember(f: &Function) -> (r: bool)
    ensures
        r == spec_gmember(*f),
{
    match &f.params {
        List::Cons((_, t), _) => matches!(t, Ty::This(_) | Ty::Iface(_) | Ty::IfaceMut(_)),
        List::Nil => false,
    }
}

/// The first implicit parameter among `todo` with the name of a parameter or a local.
pub open spec fn spec_gclash(cs: Conds, todo: Params, hide: Names, line: u32) -> Option<Refusal>
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => if spec_has(hide, g) {
            Some(Refusal::GlobalClash(g, match spec_gline(cs, g) {
                Some(l) => l,
                None => line,
            }))
        } else {
            spec_gclash(cs, *rest, hide, line)
        },
    }
}

pub fn gclash(cs: &Conds, todo: &Params, hide: &Names, line: u32) -> (r: Option<Refusal>)
    ensures
        r == spec_gclash(*cs, *todo, *hide, line),
    decreases todo,
{
    match todo {
        List::Nil => None,
        List::Cons((g, _), rest) => if has(hide, *g) {
            Some(Refusal::GlobalClash(*g, match gline(cs, *g) {
                Some(l) => l,
                None => line,
            }))
        } else {
            gclash(cs, rest, hide, line)
        },
    }
}

/// The first global among `cps`, which the callee changes, that the caller gets by value: it lists it on a reads line only.
pub open spec fn spec_greads(cps: Params, gps: Params) -> Option<u32>
    decreases cps,
{
    match cps {
        List::Nil => None,
        List::Cons((g, t), rest) => if t is Mut && match spec_get(gps, g) {
            Some(t2) => !(t2 is Mut),
            None => false,
        } {
            Some(g)
        } else {
            spec_greads(*rest, gps)
        },
    }
}

pub fn greads(cps: &Params, gps: &Params) -> (r: Option<u32>)
    ensures
        r == spec_greads(*cps, *gps),
    decreases cps,
{
    match cps {
        List::Nil => None,
        List::Cons((g, t), rest) => if matches!(t, Ty::Mut(_)) && match get(gps, *g) {
            Some(t2) => !matches!(t2, Ty::Mut(_)),
            None => false,
        } {
            Some(*g)
        } else {
            greads(rest, gps)
        },
    }
}

/// The first call among `calls` to a callee that changes a global that the caller only reads.
pub open spec fn spec_greads_call(calls: List<(u32, u32, u32)>, gs: Params, gps: Params, fs: Fns) -> Option<Refusal>
    decreases calls,
{
    match calls {
        List::Nil => None,
        List::Cons((k, nm, at), rest) => match spec_find(fs, k) {
            Some(cf) => match spec_greads(spec_gparams(cf.conds, gs), gps) {
                Some(g) => Some(Refusal::ReadsOnly(nm, g, at)),
                None => spec_greads_call(*rest, gs, gps, fs),
            },
            None => spec_greads_call(*rest, gs, gps, fs),
        },
    }
}

pub fn greads_call(calls: &List<(u32, u32, u32)>, gs: &Params, gps: &Params, fs: &Fns) -> (r: Option<Refusal>)
    ensures
        r == spec_greads_call(*calls, *gs, *gps, *fs),
    decreases calls,
{
    match calls {
        List::Nil => None,
        List::Cons((k, nm, at), rest) => match find(fs, *k) {
            Some(cf) => match greads(&gparams(&cf.conds, gs), gps) {
                Some(g) => Some(Refusal::ReadsOnly(*nm, g, *at)),
                None => greads_call(rest, gs, gps, fs),
            },
            None => greads_call(rest, gs, gps, fs),
        },
    }
}

/// The refusal of a function under decision 0173, if any: a listed global of a type with no rule, a member function that lists a
/// global, a listed global with the name of a parameter or a local, and a call that changes a global the caller only reads.
pub open spec fn spec_gcheck(f: Function, gs: Params, gps: Params, hide: Names, fs: Fns) -> Option<Refusal> {
    match spec_gtype_bad(f.conds, gs) {
        Some(r) => Some(r),
        None => match spec_glisted(f.conds, gs) {
            Some(l) => if spec_gmember(f) {
                Some(Refusal::MemberGlobal(l))
            } else {
                match spec_gclash(f.conds, gps, hide, f.line) {
                    Some(r) => Some(r),
                    None => spec_greads_call(spec_gcalls_stmts(f.body), gs, gps, fs),
                }
            },
            None => None,
        },
    }
}

pub fn gcheck(f: &Function, gs: &Params, gps: &Params, hide: &Names, fs: &Fns) -> (r: Option<Refusal>)
    ensures
        r == spec_gcheck(*f, *gs, *gps, *hide, *fs),
{
    match gtype_bad(&f.conds, gs) {
        Some(r) => Some(r),
        None => match glisted(&f.conds, gs) {
            Some(l) => if gmember(f) {
                Some(Refusal::MemberGlobal(l))
            } else {
                match gclash(&f.conds, gps, hide, f.line) {
                    Some(r) => Some(r),
                    None => greads_call(&gcalls_stmts(&f.body), gs, gps, fs),
                }
            },
            None => None,
        },
    }
}

/// The lines of a function after the pass: a reads line that names a global is consumed, and each other line also names the
/// globals of the function after its parameters, so a contract finds them, decision 0173.
pub open spec fn spec_gconds(cs: Conds, gs: Params, gnames: Names) -> Conds
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, decl), rest) => if k == CondKind::Reads && match e {
            Expr::Name(n) => spec_get(gs, n) is Some,
            _ => false,
        } {
            spec_gconds(*rest, gs, gnames)
        } else {
            List::Cons((k, e, l, spec_append(decl, gnames)), Box::new(spec_gconds(*rest, gs, gnames)))
        },
    }
}

pub fn gconds(cs: &Conds, gs: &Params, gnames: &Names) -> (r: Conds)
    ensures
        r == spec_gconds(*cs, *gs, *gnames),
    decreases cs,
{
    match cs {
        List::Nil => List::Nil,
        List::Cons((k, e, l, decl), rest) => if *k == CondKind::Reads && match e {
            Expr::Name(n) => get(gs, *n).is_some(),
            _ => false,
        } {
            gconds(rest, gs, gnames)
        } else {
            List::Cons((*k, copy_expr(e), *l, append(copy(decl), copy(gnames))), Box::new(gconds(rest, gs, gnames)))
        },
    }
}

/// No reads line among `cs` names a global of `gs`.
pub open spec fn spec_no_global_reads(cs: Conds, gs: Params) -> bool
    decreases cs,
{
    match cs {
        List::Nil => true,
        List::Cons((k, e, _, _), rest) => !(k == CondKind::Reads && match e {
            Expr::Name(n) => spec_get(gs, n) is Some,
            _ => false,
        }) && spec_no_global_reads(*rest, gs),
    }
}

/// The pass consumes each reads line that names a global, so the translator never refuses one as a word with no rule, decision 0173.
pub proof fn lemma_gconds_consume_reads(cs: Conds, gs: Params, gnames: Names)
    ensures
        spec_no_global_reads(spec_gconds(cs, gs, gnames), gs),
    decreases cs,
{
    match cs {
        List::Cons(_, rest) => lemma_gconds_consume_reads(*rest, gs, gnames),
        List::Nil => {},
    }
}

/// Each function after the pass holds no reads line that names a global.
pub proof fn lemma_globalize_consumes_reads(f: Function, gs: Params, fs: Fns)
    ensures
        spec_no_global_reads(spec_globalize_fn(f, gs, fs).conds, gs),
{
    let gps = spec_gparams(f.conds, gs);
    let hide = spec_append(spec_keys(f.params), spec_glocals(f.body));
    lemma_gconds_consume_reads(f.conds, gs, spec_keys(gps));
    if let Some(r) = spec_gcheck(f, gs, gps, hide, fs) {
        assert(spec_globalize_fn(f, gs, fs).conds == List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(spec_gconds(f.conds, gs, spec_keys(gps)))));
    }
}

/// One function after the pass of decision 0173. A refusal of the pass is a line that the translator refuses first.
pub open spec fn spec_globalize_fn(f: Function, gs: Params, fs: Fns) -> Function {
    let gps = spec_gparams(f.conds, gs);
    let hide = spec_append(spec_keys(f.params), spec_glocals(f.body));
    let cs = spec_gconds(f.conds, gs, spec_keys(gps));
    Function {
        name: f.name,
        line: f.line,
        params: spec_append(f.params, gps),
        ret: f.ret,
        trusted: f.trusted,
        conds: match spec_gcheck(f, gs, gps, hide, fs) {
            Some(r) => List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(cs)),
            None => cs,
        },
        body: spec_gstmts(f.body, gs, gps, hide, fs),
    }
}

pub fn globalize_fn(f: &Function, gs: &Params, fs: &Fns) -> (r: Function)
    ensures
        r == spec_globalize_fn(*f, *gs, *fs),
{
    let gps = gparams(&f.conds, gs);
    let hide = append(keys(&f.params), glocals(&f.body));
    let cs = gconds(&f.conds, gs, &keys(&gps));
    let conds = match gcheck(f, gs, &gps, &hide, fs) {
        Some(r) => List::Cons((CondKind::Bad(r), Expr::Bool(true), f.line, List::Nil), Box::new(cs)),
        None => cs,
    };
    let body = gstmts(&f.body, gs, &gps, &hide, fs);
    Function { name: f.name, line: f.line, params: append(copy(&f.params), gps), ret: f.ret, trusted: f.trusted, conds, body }
}

pub open spec fn spec_globalize_all(todo: Fns, gs: Params, fs: Fns) -> Fns
    decreases todo,
{
    match todo {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(Box::new(spec_globalize_fn(*f, gs, fs)), Box::new(spec_globalize_all(*rest, gs, fs))),
    }
}

pub fn globalize_all(todo: &Fns, gs: &Params, fs: &Fns) -> (r: Fns)
    ensures
        r == spec_globalize_all(*todo, *gs, *fs),
    decreases todo,
{
    match todo {
        List::Nil => List::Nil,
        List::Cons(f, rest) => List::Cons(Box::new(globalize_fn(f, gs, fs)), Box::new(globalize_all(rest, gs, fs))),
    }
}

/// The pass of decision 0173, which the shell runs before translate_unit: each function of the file with the globals `gs` that it
/// lists as implicit parameters.
pub open spec fn spec_globalize(fs: Fns, gs: Params) -> Fns {
    spec_globalize_all(fs, gs, fs)
}

pub fn globalize(fs: &Fns, gs: &Params) -> (r: Fns)
    ensures
        r == spec_globalize(*fs, *gs),
{
    globalize_all(fs, gs, fs)
}

// ------------------------------------------------------------------ static member functions, decision 0174

/// A static member function of a struct of the file by the id of its name: a member whose twin takes no object, `this` of a struct
/// or of an interface. A static can take a struct as its first argument. A static has its
/// qualified name, `Tally::valid`, so it never meets a const member, whose name is plain. A member with no twin is taken as a
/// static here too, so a contract that calls it is refused.
// ponytail: a companion function with the plain name of a member with no twin of some struct is refused as no pure member
// function. Upgrade: a flag for a static in the table of members.
pub open spec fn spec_static(sd: Structs, f: u32) -> Option<(u32, Option<(Ty, Params)>)>
    decreases sd,
{
    match sd {
        List::Nil => None,
        List::Cons((_, (_, _, ms)), rest) => match spec_get(ms, f) {
            Some((key, Some((t, mps)))) => if spec_head_ty(mps) is Some && (spec_head_ty(mps)->Some_0 is This || spec_head_ty(mps)->Some_0 is Iface) {
                spec_static(*rest, f)
            } else {
                Some((key, Some((t, mps))))
            },
            Some((key, None)) => Some((key, None)),
            None => spec_static(*rest, f),
        },
    }
}

pub fn static_of(sd: &Structs, f: u32) -> (r: Option<(u32, Option<(Ty, Params)>)>)
    ensures
        r == spec_static(*sd, f),
    decreases sd,
{
    match sd {
        List::Nil => None,
        List::Cons((_, (_, _, ms)), rest) => match get_ref(ms, f) {
            Some((key, Some((t, mps)))) => if match mps {
                List::Cons((_, t0), _) => matches!(t0, Ty::This(_) | Ty::Iface(_)),
                List::Nil => false,
            } {
                static_of(rest, f)
            } else {
                Some((*key, Some((*t, copy(mps)))))
            },
            Some((key, None)) => Some((*key, None)),
            None => static_of(rest, f),
        },
    }
}

/// The parameters of a twin after those that the arguments of the call fill.
pub open spec fn spec_drop_params(mps: Params, args: Args) -> Params
    decreases args,
{
    match args {
        List::Nil => mps,
        List::Cons(_, rest) => match mps {
            List::Nil => List::Nil,
            List::Cons(_, prest) => spec_drop_params(*prest, *rest),
        },
    }
}

pub fn drop_params(mps: &Params, args: &Args) -> (r: Params)
    ensures
        r == spec_drop_params(*mps, *args),
    decreases args,
{
    match args {
        List::Nil => copy(mps),
        List::Cons(_, rest) => match mps {
            List::Nil => List::Nil,
            List::Cons(_, prest) => drop_params(prest, rest),
        },
    }
}

/// The values of the globals `gps` of a twin, as the contract line reads each by its name: before in a requires line and under
/// `old`, after in an ensures line. A global that the function lists on no line is no parameter, so the line is refused.
pub open spec fn spec_gvals(gps: Params, decl: Names, ps: Params, line: u32) -> Result<DArgs, Refusal>
    decreases gps,
{
    match gps {
        List::Nil => Ok(List::Nil),
        List::Cons((g, _), rest) => match spec_rebind(decl, ps, g) {
            Some((p, t)) => match spec_gvals(*rest, decl, ps, line) {
                Ok(dr) => Ok(List::Cons(spec_var(p, t), Box::new(dr))),
                Err(r) => Err(r),
            },
            None => Err(Refusal::Name(g, line)),
        },
    }
}

pub fn gvals(gps: &Params, decl: &Names, ps: &Params, line: u32) -> (r: Result<DArgs, Refusal>)
    ensures
        r == spec_gvals(*gps, *decl, *ps, line),
    decreases gps,
{
    match gps {
        List::Nil => Ok(List::Nil),
        List::Cons((g, _), rest) => match rebind(decl, ps, *g) {
            Some((p, t)) => match gvals(rest, decl, ps, line) {
                Ok(dr) => Ok(List::Cons(contract_var(p, t), Box::new(dr))),
                Err(r) => Err(r),
            },
            None => Err(Refusal::Name(*g, line)),
        },
    }
}

/// A call `f(a)` of a contract with the arguments `da` that names no member of the object: the twin of a static member function
/// with its globals after the arguments, decision 0174, or else a function of the companion file, decision 0079.
pub open spec fn spec_static_value(f: u32, da: DArgs, args: Args, decl: Names, ps: Params, line: u32, sd: Structs) -> Result<DExpr, Refusal> {
    match spec_static(sd, f) {
        Some((key, Some((t, mps)))) => match spec_gvals(spec_drop_params(mps, args), decl, ps, line) {
            Ok(dg) => spec_leaf(DExpr::FCall(key, Box::new(spec_append(spec_convert(da, mps), dg))), t, line),
            Err(r) => Err(r),
        },
        Some((_, None)) => Err(Refusal::NotPure(f, line)),
        None => Ok(DExpr::Apply(f, Box::new(da))),
    }
}

pub fn static_value(f: u32, da: DArgs, args: &Args, decl: &Names, ps: &Params, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_static_value(f, da, *args, *decl, *ps, line, *sd),
{
    match static_of(sd, f) {
        Some((key, Some((t, mps)))) => match gvals(&drop_params(&mps, args), decl, ps, line) {
            Ok(dg) => translate_leaf(DExpr::FCall(key, Box::new(append(convert(da, &mps), dg))), t, line),
            Err(r) => Err(r),
        },
        Some((_, None)) => Err(Refusal::NotPure(f, line)),
        None => Ok(DExpr::Apply(f, Box::new(da))),
    }
}

} // verus!

//! The translator: the C++ side. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

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
/// its object, decision 0169. `Ptr` is a raw pointer parameter to one object, decisions 0140 and 0141, and `Own` is a
/// `std::unique_ptr`, decision 0142. `Variant` is a `std::variant` of two different element types, decision 0202. `Void` is the result type
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
    Variant(Scalar, Scalar),
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
/// value `v(n, x)` of a local vector, by the count and the value, decision 0185. `Either` is `o.size()`, `o.empty()` or `o.back()` in a contract, as the form of a sequence and the id of the name of a
/// member, and the translator picks one by the type of `o`, decision 0200. `Back` is `v.back()` of a vector in code, decision 0191, and `EmptyVec` is an empty
/// vector `{}` in code. `Holds`
/// is `std::holds_alternative<T>(v)` and `GetAlt` is `std::get<T>(v)` of a variant, by the type `T`, decision 0202. `Unknown` is a construct with no rule, by the id of
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
    Back(Box<Expr>),
    Either(Box<Expr>, u32),
    Holds(Ty, Box<Expr>),
    GetAlt(Ty, Box<Expr>),
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
/// std::array, decision 0184. `PushBack` is `v.push_back(e)`, decision 0148. `PushField` and `PopField`
/// are `f.push_back(e)` and `f.pop_back()` of a sequence field of the object, decision 0191.
/// `Sort` is `std::sort(v.begin(), v.end())`, decision 0161, and `SortBy` is the same with a comparator lambda, by the names and the
/// type of its two parameters and the expression of its one `return`, decision 0162. `Block` is a bare block `{ ... }`, a scope of
/// its own, decision 0178. `SetOwnField` is `n->f = e` of a local `std::unique_ptr` of a plain struct, decision 0186. `SetFieldAt` is
/// `f[i] = e` of a sequence field in a member function that writes its object, decision 0187. `SetThroughField` is `f->g = e` of a
/// `std::unique_ptr` field `f` of the object, decision 0197.
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
    PushField(u32, Expr, u32),
    PopField(u32, u32),
    SetThroughField(u32, u32, Expr, u32),
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
/// global that the function reads, decision 0173. `Index` names the index of a range-for, decision 0143. `Other` is a word
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

} // verus!

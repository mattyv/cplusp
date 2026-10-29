//! The translator: the Dafny side. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ the Dafny side

/// A Dafny type. `Arr` is a sequence that holds its length, `Arr'N<T>`: the type of a `std::array` field, decision 0196.
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
    Arr(Scalar, u64),
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
    Back(Box<DExpr>),
    PopBack(Box<DExpr>),
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
/// 0104. `SetOwnField` is `n := Some(n.value.(f := e));` of a local unique_ptr, decision 0186. `SetThroughField` is
/// `this' := this'.(f := Some(this'.f.value.(g := e)));`, decision 0197.
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
    SetThroughField(u32, u32, DExpr),
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
/// 0169. `Field` is a vector field of the object of the member function, whose element a call writes, decision 0204.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Obj {
    Local(u32),
    Object,
    Out(u32),
    Owned(u32),
    Field(u32),
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
/// with no rule, by the line, decision 0171. `VecMovePlace` is the same for a move of a vector, decision 0195. `ReadsOnly` is a call that changes a global that the caller lists on its reads line only,
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
    VecMovePlace(u32),
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

} // verus!

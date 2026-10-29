//! The translator: the rules. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

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
        // A variant of two different element types, decision 0202.
        Ty::Variant(Scalar::Own(_), _) => Err(Refusal::Element(line)),
        Ty::Variant(_, Scalar::Own(_)) => Err(Refusal::Element(line)),
        Ty::Variant(a, b) => if a != b { Ok(DTy::Variant(a, b)) } else { Err(Refusal::Element(line)) },
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

/// The callee `key` is a const virtual function of an interface, a function of the model with no body, decision 0172, or a plain
/// member function that the table `sd` marks pure, decision 0189. A call of it is that function in any place of code, because it
/// changes no state.
pub open spec fn spec_inline(all: Fns, key: u32, sd: Structs) -> bool {
    match spec_find(all, key) {
        Some(f) => spec_const_virtual(f) || (spec_plain(f) && spec_key_pure(sd, key)),
        None => false,
    }
}

pub fn inline(all: &Fns, key: u32, sd: &Structs) -> (r: bool)
    ensures
        r == spec_inline(*all, key, *sd),
{
    match find(all, key) {
        Some(f) => const_virtual(f) || (plain(f) && key_pure(sd, key)),
        None => false,
    }
}

/// A plain member function: a const member function with no reference parameter that it writes, whose body is a plain body,
/// decisions 0189 and 0211. It calls no function, so a call of it can never be part of a cycle.
pub open spec fn spec_plain(f: Function) -> bool {
    !f.trusted && (spec_head_ty(f.params) matches Some(Ty::This(_))) && !spec_mutates(f.params) && spec_plain_body(f.body)
}

/// A plain body: apply lines, then one `return` of an expression with no call, decisions 0189 and 0211. An apply line calls a lemma,
/// which changes no value.
pub open spec fn spec_plain_body(ss: Stmts) -> bool
    decreases ss,
{
    match ss {
        List::Cons(st, rest) => match *st {
            Stmt::Return(e, _) => *rest == List::Nil && spec_gcalls(e) == List::<(u32, u32, u32)>::Nil,
            Stmt::Apply(_, _, _) => spec_plain_body(*rest),
            _ => false,
        },
        List::Nil => false,
    }
}

pub fn plain(f: &Function) -> (r: bool)
    ensures
        r == spec_plain(*f),
{
    !f.trusted && matches!(head_ty(&f.params), Some(Ty::This(_))) && !mutates(&f.params) && plain_body(&f.body)
}

pub fn plain_body(ss: &Stmts) -> (r: bool)
    ensures
        r == spec_plain_body(*ss),
    decreases ss,
{
    match ss {
        List::Cons(st, rest) => match &**st {
            Stmt::Return(e, _) => matches!(&**rest, List::Nil) && matches!(gcalls(e), List::Nil),
            Stmt::Apply(_, _, _) => plain_body(rest),
            _ => false,
        },
        List::Nil => false,
    }
}

/// A member of a struct of `sd` with the key `key` is marked pure, with a type that is no mark of a member with no function,
/// decisions 0095 and 0188.
pub open spec fn spec_key_pure(sd: Structs, key: u32) -> bool
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => spec_members_key_pure(ms, key) || spec_key_pure(*rest, key),
    }
}

pub open spec fn spec_members_key_pure(ms: Members, key: u32) -> bool
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (k, m)), rest) => (k == key && match m {
            Some((t, _)) => !(t is Other),
            None => false,
        }) || spec_members_key_pure(*rest, key),
    }
}

pub fn key_pure(sd: &Structs, key: u32) -> (r: bool)
    ensures
        r == spec_key_pure(*sd, key),
    decreases sd,
{
    match sd {
        List::Nil => false,
        List::Cons((_, (_, _, ms)), rest) => members_key_pure(ms, key) || key_pure(rest, key),
    }
}

pub fn members_key_pure(ms: &Members, key: u32) -> (r: bool)
    ensures
        r == spec_members_key_pure(*ms, key),
    decreases ms,
{
    match ms {
        List::Nil => false,
        List::Cons((_, (k, m)), rest) => (*k == key && match m {
            Some((t, _)) => !matches!(t, Ty::Other(_)),
            None => false,
        }) || members_key_pure(rest, key),
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
        // A call of a const virtual function of an interface, decision 0172, or of a plain member function, decision 0189, is its
        // function in place.
        Expr::Call(k, nm, args, at) => if spec_inline(all, k, sd) && spec_callable(all, k, sd) {
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
        // `v.back()` is Back of the prelude, whose requires line Dafny checks, decision 0191.
        Expr::Back(o) => match spec_lift(*o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Back(Box::new(d)), n1)),
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
        // `std::holds_alternative<T>(v)` and `std::get<T>(v)` of a variant parameter, decision 0202.
        Expr::Holds(t, o) => match spec_code_alt(false, t, *o, line) {
            Ok(d) => Ok((List::Nil, d, n)),
            Err(r) => Err(r),
        },
        Expr::GetAlt(t, o) => match spec_code_alt(true, t, *o, line) {
            Ok(d) => Ok((List::Nil, d, n)),
            Err(r) => Err(r),
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
        // A move that the statement did not take out stands in a place with no rule, decision 0171. A move of a vector has its own
        // sentence, decision 0195.
        Expr::Move(_, Ty::Vec(_)) => Err(Refusal::VecMovePlace(line)),
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
        Expr::Back(f0) => Expr::Back(Box::new(copy_expr(f0))),
        Expr::Either(f0, f1) => Expr::Either(Box::new(copy_expr(f0)), *f1),
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
        Expr::Holds(f0, f1) => Expr::Holds(*f0, Box::new(copy_expr(f1))),
        Expr::GetAlt(f0, f1) => Expr::GetAlt(*f0, Box::new(copy_expr(f1))),
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
        Expr::Back(f0) => spec_var_names(*f0),
        Expr::Either(f0, _) => spec_var_names(*f0),
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
        Expr::Holds(_, f1) => spec_var_names(*f1),
        Expr::GetAlt(_, f1) => spec_var_names(*f1),
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
        Expr::Back(f0) => var_names(f0),
        Expr::Either(f0, _) => var_names(f0),
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
        Expr::Holds(_, f1) => var_names(f1),
        Expr::GetAlt(_, f1) => var_names(f1),
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
pub open spec fn spec_nulled(d: DStmt, ns: Names) -> DStmt {
    match ns {
        List::Nil => d,
        _ => DStmt::Moved(Box::new(d), ns),
    }
}

pub fn nulled(d: DStmt, ns: Names) -> (r: DStmt)
    ensures
        r == spec_nulled(d, ns),
{
    match ns {
        List::Nil => d,
        _ => DStmt::Moved(Box::new(d), ns),
    }
}

/// The statement, then each vector of `vs` with any value, decisions 0185 and 0194.
pub open spec fn spec_gone_all(d: DStmt, vs: Names) -> DStmt
    decreases vs,
{
    match vs {
        List::Nil => d,
        List::Cons(w, rest) => spec_gone_all(DStmt::Gone(Box::new(d), w, false), *rest),
    }
}

pub fn gone_all(d: DStmt, vs: &Names) -> (r: DStmt)
    ensures
        r == spec_gone_all(d, *vs),
    decreases vs,
{
    match vs {
        List::Nil => d,
        List::Cons(w, rest) => gone_all(DStmt::Gone(Box::new(d), *w, false), rest),
    }
}

/// The names of `ns` that are not in `vs`.
pub open spec fn spec_without(ns: Names, vs: Names) -> Names
    decreases ns,
{
    match ns {
        List::Nil => List::Nil,
        List::Cons(n, rest) => if spec_has(vs, n) {
            spec_without(*rest, vs)
        } else {
            List::Cons(n, Box::new(spec_without(*rest, vs)))
        },
    }
}

pub fn without(ns: &Names, vs: &Names) -> (r: Names)
    ensures
        r == spec_without(*ns, *vs),
    decreases ns,
{
    match ns {
        List::Nil => List::Nil,
        List::Cons(n, rest) => if has(vs, *n) {
            without(rest, vs)
        } else {
            List::Cons(*n, Box::new(without(rest, vs)))
        },
    }
}

/// A statement that moves the names `ns`, of which `vs` are vectors. A unique_ptr is null after it, decision 0171, and a vector
/// has any value, decisions 0185 and 0194.
pub open spec fn spec_moved(d: DStmt, ns: Names, vs: Names) -> DStmt {
    spec_gone_all(spec_nulled(d, spec_without(ns, vs)), vs)
}

pub fn moved(d: DStmt, ns: Names, vs: Names) -> (r: DStmt)
    ensures
        r == spec_moved(d, ns, vs),
{
    let w = without(&ns, &vs);
    gone_all(nulled(d, w), &vs)
}

/// The names of the vectors that an expression moves, in the places that `spec_unmove` reads, decision 0194.
pub open spec fn spec_vec_moves(e: Expr) -> Names
    decreases e,
{
    match e {
        Expr::Move(v, Ty::Vec(_)) => List::Cons(v, Box::new(List::Nil)),
        Expr::Call(_, _, args, _) => spec_vec_moves_args(*args),
        Expr::Construct(_, args) => spec_vec_moves_args(*args),
        Expr::Wrap(a) => spec_vec_moves(*a),
        Expr::Cast(_, a) => spec_vec_moves(*a),
        Expr::Paren(a) => spec_vec_moves(*a),
        _ => List::Nil,
    }
}

pub open spec fn spec_vec_moves_args(args: Args) -> Names
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => spec_append(spec_vec_moves(*a), spec_vec_moves_args(*rest)),
    }
}

pub fn vec_moves(e: &Expr) -> (r: Names)
    ensures
        r == spec_vec_moves(*e),
    decreases e,
{
    match e {
        Expr::Move(v, Ty::Vec(_)) => List::Cons(*v, Box::new(List::Nil)),
        Expr::Call(_, _, args, _) => vec_moves_args(args),
        Expr::Construct(_, args) => vec_moves_args(args),
        Expr::Wrap(a) => vec_moves(a),
        Expr::Cast(_, a) => vec_moves(a),
        Expr::Paren(a) => vec_moves(a),
        _ => List::Nil,
    }
}

pub fn vec_moves_args(args: &Args) -> (r: Names)
    ensures
        r == spec_vec_moves_args(*args),
    decreases args,
{
    match args {
        List::Nil => List::Nil,
        List::Cons(a, rest) => append(vec_moves(a), vec_moves_args(rest)),
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

/// The alternative of the variant of `a` and `b` whose type is `t`: false for `a`, true for `b`, decision 0202.
pub open spec fn spec_alt_index(t: Ty, a: Scalar, b: Scalar) -> Option<bool> {
    if spec_elem(a) == t {
        Some(false)
    } else if spec_elem(b) == t {
        Some(true)
    } else {
        None
    }
}

/// `std::holds_alternative<T>(v)`, or `std::get<T>(v)` when `get` holds, of a variant parameter `v` in code, decision 0202.
pub open spec fn spec_code_alt(get: bool, t: Ty, o: Expr, line: u32) -> Result<DExpr, Refusal> {
    match o {
        Expr::Var(v, Ty::Variant(a, b)) => match spec_alt_index(t, a, b) {
            Some(i) => Ok(if get {
                DExpr::Alt(i, Box::new(spec_code_var(v, Ty::Variant(a, b))))
            } else {
                DExpr::Is(i, Box::new(spec_code_var(v, Ty::Variant(a, b))))
            }),
            None => Err(Refusal::Syntax(line)),
        },
        _ => Err(Refusal::Syntax(line)),
    }
}

/// The member function `f` of a value of type `t` that a contract calls: the key of its function, its result type and its
/// parameters, decision 0090. A type with no member table has no member function.
pub open spec fn spec_member_of(t: Ty, f: u32, line: u32, sd: Structs) -> Result<(u32, Ty, Params), Refusal> {
    match spec_struct_key(t) {
        Some(k) => match spec_member(sd, k, f) {
            Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
            Some((key, Some((rt, mps)))) => Ok((key, rt, mps)),
            _ => Err(Refusal::NotPure(f, line)),
        },
        None => Err(Refusal::Syntax(line)),
    }
}

/// A call with no argument of the member function `f` on the value `d` of type `t`, decision 0200.
pub open spec fn spec_nullary(d: DExpr, t: Ty, f: u32, line: u32, sd: Structs) -> Result<DExpr, Refusal> {
    match spec_member_of(t, f, line, sd) {
        Ok((key, rt, _)) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(List::Nil)))), rt, line),
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
        // `o.size()`, `o.empty()` and `o.back()` read a sequence, and call the member of that name of any other type, decision 0200.
        // The object is read once, so a chain of them is read in a time that grows with its length.
        Expr::Either(s, id) => match *s {
            Expr::Size(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Len(Box::new(d))),
                Ok((d, t)) => spec_nullary(d, t, id, line, sd),
                Err(r) => Err(r),
            },
            Expr::Empty(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
                Ok((d, t)) => spec_nullary(d, t, id, line, sd),
                Err(r) => Err(r),
            },
            Expr::Back(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Seq(s, _))) => spec_leaf(DExpr::Back(Box::new(d)), spec_elem(s), line),
                Ok((d, t)) => spec_nullary(d, t, id, line, sd),
                Err(r) => Err(r),
            },
            _ => Err(Refusal::Syntax(line)),
        },
        Expr::Back(o) => match spec_path(Expr::Back(o), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
            Err(r) => Err(r),
        },
        // `std::holds_alternative<T>(v)` is a test of the constructor of the datatype, decision 0202.
        Expr::Holds(t, o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Variant(a, b))) => match spec_alt_index(t, a, b) {
                Some(i) => Ok(DExpr::Is(i, Box::new(d))),
                None => Err(Refusal::Syntax(line)),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        Expr::GetAlt(t, o) => match spec_path(Expr::GetAlt(t, o), decl, ps, ret, bound, line, sd) {
            Ok((d, t)) => spec_leaf(d, t, line),
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
                    Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
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
                Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
                Some((key, Some((rt, mps)))) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match spec_object(ps, ret) {
            Some((o, k)) => match spec_member(sd, k, f) {
                // A member with no function of the file, decision 0188.
                Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
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
            // `a.count()` of a duration is its count, an int64, decision 0175.
            Ok((d, t)) => if f == COUNT_NAME && *args is Nil && t == Ty::I64 {
                spec_leaf(d, t, line)
            } else {
                match spec_member_of(t, f, line, sd) {
                    Ok((key, rt, mps)) => match spec_contract_args(*args, decl, ps, ret, bound, line, sd) {
                        Ok(da) => spec_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(spec_convert(da, spec_tail(mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                }
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
        // Dafny orders two variants by a rank that C++ does not know, as two enums, decision 0206.
        _ => match spec_path(e, decl, ps, ret, bound, line, sd) {
            Ok((_, Ty::Enum(_))) => true,
            Ok((_, Ty::Variant(_, _))) => true,
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
        // `o.back()` of a sequence is its last element, decision 0200. A call of a member function is no path.
        Expr::Either(s, _) => match *s {
            Expr::Back(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Seq(s, _))) => Ok((DExpr::Back(Box::new(d)), spec_elem(s))),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            },
            _ => Err(Refusal::Syntax(line)),
        },
        // `std::get<T>(v)` is the value of the alternative, which Dafny proves the variant holds, decision 0202.
        Expr::GetAlt(t, o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Variant(a, b))) => match spec_alt_index(t, a, b) {
                Some(i) => Ok((DExpr::Alt(i, Box::new(d)), t)),
                None => Err(Refusal::Syntax(line)),
            },
            Ok(_) => Err(Refusal::Syntax(line)),
            Err(r) => Err(r),
        },
        // `v.back()` is the last element, decision 0191.
        Expr::Back(o) => match spec_path(*o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => Ok((DExpr::Back(Box::new(d)), spec_elem(s))),
            Ok(_) => Err(Refusal::Syntax(line)),
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
        // A vector by value of a struct that holds a sequence, decision 0194.
        Ty::Vec(Scalar::Struct(k)) => if spec_holds(sd, k) {
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
        Stmt::PushField(_, _, l) => l,
        Stmt::SetThroughField(_, _, _, l) => l,
        Stmt::PopField(_, l) => l,
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

} // verus!

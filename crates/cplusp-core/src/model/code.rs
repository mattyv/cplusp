//! The translator: the code that runs. The summary of the proofs is in `model`.

use super::*;
use super::rules::real;
use vstd::prelude::*;

verus! {

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
        Expr::Call(k, nm, args, at) => if inline(all, *k, sd) && callable(all, *k, sd) {
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
        Expr::Back(o) => match lift(o, all, line, sd, n, open) {
            Err(r) => Err(r),
            Ok((c, d, n1)) => Ok((c, DExpr::Back(Box::new(d)), n1)),
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
        Expr::Move(_, Ty::Vec(_)) => Err(Refusal::VecMovePlace(line)),
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

pub fn member_of(t: Ty, f: u32, line: u32, sd: &Structs) -> (r: Result<(u32, Ty, Params), Refusal>)
    ensures
        r == spec_member_of(t, f, line, *sd),
{
    match struct_key(t) {
        Some(k) => match member(sd, k, f) {
            Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
            Some((key, Some((rt, mps)))) => Ok((key, rt, mps)),
            _ => Err(Refusal::NotPure(f, line)),
        },
        None => Err(Refusal::Syntax(line)),
    }
}

pub fn nullary(d: DExpr, t: Ty, f: u32, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_nullary(d, t, f, line, *sd),
{
    match member_of(t, f, line, sd) {
        Ok((key, rt, _)) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(List::Nil)))), rt, line),
        Err(r) => Err(r),
    }
}

pub fn translate_either(s: &Expr, id: u32, decl: &Names, ps: &Params, ret: Option<Ty>, bound: &Names, line: u32, sd: &Structs) -> (r: Result<DExpr, Refusal>)
    ensures
        r == spec_contract(Expr::Either(Box::new(*s), id), *decl, *ps, ret, *bound, line, *sd),
    decreases s, 2nat,
{
    match s {
        Expr::Size(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Len(Box::new(d))),
            Ok((d, t)) => nullary(d, t, id, line, sd),
            Err(r) => Err(r),
        },
        Expr::Empty(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(_, _))) => Ok(DExpr::Bin(BinOp::Eq, Box::new(DExpr::Len(Box::new(d))), Box::new(DExpr::Lit(0)))),
            Ok((d, t)) => nullary(d, t, id, line, sd),
            Err(r) => Err(r),
        },
        Expr::Back(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => translate_leaf(DExpr::Back(Box::new(d)), elem(s), line),
            Ok((d, t)) => nullary(d, t, id, line, sd),
            Err(r) => Err(r),
        },
        _ => Err(Refusal::Syntax(line)),
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
        // `o.size()`, `o.empty()` and `o.back()` read a sequence, and call the member of that name of any other type, decision 0200.
        Expr::Either(s, id) => translate_either(s, *id, decl, ps, ret, bound, line, sd),
        Expr::Index(_, _) | Expr::Back(_) | Expr::Suffix(_, _) | Expr::Prefix(_, _) | Expr::Slice(_, _, _) => match path(e, decl, ps, ret, bound, line, sd) {
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
                    Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
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
                Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
                Some((key, Some((rt, mps)))) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                    Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::NotPure(CALL_OP, line)),
            },
            None => match object(ps, ret) {
            Some((o, k)) => match member(sd, k, *f) {
                Some((key, Some((Ty::Other(_), _)))) => Err(Refusal::Callee(key, line)),
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
            Ok((d, t)) => if *f == COUNT_NAME && matches!(**args, List::Nil) && t == Ty::I64 {
                translate_leaf(d, t, line)
            } else {
                match member_of(t, *f, line, sd) {
                    Ok((key, rt, mps)) => match translate_contract_args(args, decl, ps, ret, bound, line, sd) {
                        Ok(da) => translate_leaf(DExpr::FCall(key, Box::new(List::Cons(d, Box::new(convert(da, &tail(&mps)))))), rt, line),
                        Err(r) => Err(r),
                    },
                    Err(r) => Err(r),
                }
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
        Expr::Either(s, _) => match &**s {
            Expr::Back(o) => match path(o, decl, ps, ret, bound, line, sd) {
                Ok((d, Ty::Seq(s, _))) => Ok((DExpr::Back(Box::new(d)), elem(s))),
                Ok(_) => Err(Refusal::Syntax(line)),
                Err(r) => Err(r),
            },
            _ => Err(Refusal::Syntax(line)),
        },
        Expr::Back(o) => match path(o, decl, ps, ret, bound, line, sd) {
            Ok((d, Ty::Seq(s, _))) => Ok((DExpr::Back(Box::new(d)), elem(s))),
            Ok(_) => Err(Refusal::Syntax(line)),
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
        Ty::Vec(Scalar::Struct(k)) => if holds_seq(sd, k) {
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
        Stmt::PushField(_, _, l) => *l,
        Stmt::SetThroughField(_, _, _, l) => *l,
        Stmt::PopField(_, l) => *l,
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

pub fn field_elem<'a>(o: &'a Expr, ps: &Params, sd: &Structs) -> (r: Option<(u32, &'a Expr)>)
    ensures
        match r {
            Some((f, i)) => spec_field_elem(*o, *ps, *sd) == Some((f, *i)),
            None => spec_field_elem(*o, *ps, *sd) is None,
        },
    decreases o,
{
    match o {
        Expr::Value(a) => match &**a {
            Expr::Index(v, i) => match &**v {
                Expr::Field(t, f) => match &**t {
                    Expr::Var(p, Ty::ThisMut(k)) => if self_param(ps) == Some((*p, Ty::ThisMut(*k))) {
                        match field_ty(sd, *k, *f) {
                            Some(Ty::Seq(Scalar::Own(_), Extent::Dynamic)) => Some((*f, &**i)),
                            _ => None,
                        }
                    } else {
                        None
                    },
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        Expr::Cast(c, a) => if *c == CastKind::Read || *c == CastKind::NoOp {
            field_elem(a, ps, sd)
        } else {
            None
        },
        Expr::Paren(a) => field_elem(a, ps, sd),
        _ => None,
    }
}

pub fn elem_place<'a>(o: &'a Expr, ps: &Params, line: u32, sd: &Structs) -> (r: Option<(Result<Obj, Refusal>, &'a Expr, Option<u32>)>)
    ensures
        match r {
            Some((p, i, v)) => spec_elem_place(*o, *ps, line, *sd) == Some((p, *i, v)),
            None => spec_elem_place(*o, *ps, line, *sd) is None,
        },
{
    match elem_object(o) {
        Some((v, t, i)) => Some((vec_obj(v, t, ps, line), i, Some(v))),
        None => match field_elem(o, ps, sd) {
            Some((f, i)) => Some((Ok(Obj::Field(f)), i, None)),
            None => None,
        },
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
        Obj::Field(_) => false,
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
                List::Cons(a, rest) => match elem_place(a, ps, line, sd) {
                    Some((place, i, vn)) => Some(match place {
                        Err(r) => Err(r),
                        Ok(vo) => match writebacks(rest, &tail(&f.params), ps, line) {
                            Err(r) => Err(r),
                            Ok(os) => match index_vars(i) {
                                None => Err(Refusal::IndexWritten(line)),
                                Some(ns) => if (match vn { Some(v) => has(&ns, v), None => false }) || writes_name(&os, &ns) {
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

pub fn push_field(f: u32, e: &Expr, l: u32, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_push_field(f, *e, l, *ps, *sd),
{
    match self_param(ps) {
        Some((p, t)) => match t {
            Ty::ThisMut(k) => match field_ty(sd, k, f) {
                Some(Ty::Seq(_, _)) => {
                    let (ue, ns) = unmove(e);
                    match move_check(&ns, &var_names(e), ps, false, l) {
                        Some(r) => Err(r),
                        None => match translate_code(&ue, l) {
                            Ok(de) => Ok(moved(
                                DStmt::SetField(f, DExpr::Append(Box::new(DExpr::Field(Box::new(DExpr::After), f)), Box::new(de))),
                                ns,
                                vec_moves(e),
                            )),
                            Err(r) => Err(r),
                        },
                    }
                },
                Some(_) => Err(Refusal::Syntax(l)),
                None => Err(Refusal::NoField(f, l)),
            },
            _ => Err(Refusal::WriteParam(p, l)),
        },
        None => Err(Refusal::Syntax(l)),
    }
}

pub fn push_back(v: u32, e: &Expr, l: u32, all: &Fns, env: &Params, ps: &Params, sd: &Structs) -> (r: Result<DStmt, Refusal>)
    ensures
        r == spec_push_back(v, *e, l, *all, *env, *ps, *sd),
{
    let (ue, ns) = unmove(e);
    match move_check(&ns, &List::Cons(v, Box::new(var_names(e))), ps, false, l) {
        Some(r) => Err(r),
        None => match get(ps, v) {
            Some(Ty::MutSeq(_)) => match push_value(&ue, all, l, sd) {
                Ok((c, de)) => Ok(moved(pre(c, DStmt::SetOut(v, DExpr::Append(Box::new(DExpr::Out(v)), Box::new(de)))), ns, vec_moves(e))),
                Err(r) => Err(r),
            },
            Some(_) => Err(Refusal::WriteParam(v, l)),
            None => match get(env, v) {
                Some(Ty::Vec(_)) => match push_value(&ue, all, l, sd) {
                    Ok((c, de)) => Ok(moved(pre(c, DStmt::Assign(v, DExpr::Append(Box::new(DExpr::Var(v)), Box::new(de)))), ns, vec_moves(e))),
                    Err(r) => Err(r),
                },
                _ => Err(Refusal::Syntax(l)),
            },
        },
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
            Expr::Fill(c, x) => match &**c {
                Expr::Lit(m, _) => if *m == *k {
                    match translate_ty(Ty::Seq(*s, Extent::Fixed(*k)), *l) {
                        Err(r) => Err(r),
                        Ok(dt) => match lift(x, all, *l, sd, 0, true) {
                            Ok((cx, dx, _)) => Ok(pre(cx, DStmt::Local(*n, dt, DExpr::SeqFill(Box::new(DExpr::Conv(DTy::UInt64, Box::new(DExpr::Lit(*m)))), Box::new(dx))))),
                            Err(r) => Err(r),
                        },
                    }
                } else {
                    Err(Refusal::SeqParam(*l))
                },
                _ => Err(Refusal::SeqParam(*l)),
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
                            Ok(d) => Ok(moved(d, ns, vec_moves(e))),
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
                                Ok((c, d, _)) => Ok(moved(pre(c, DStmt::SetOwnField(*n, *f, d)), ns, vec_moves(e))),
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
                    Ok(d) => Ok(moved(d, ns, vec_moves_args(args))),
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
        Stmt::SetThroughField(f, g, e, l) => match self_param(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match field_ty(sd, k, *f) {
                    Some(Ty::Own(Scalar::Struct(k2))) => match field_ty(sd, k2, *g) {
                        Some(Ty::Seq(_, _)) => Err(Refusal::SeqParam(*l)),
                        Some(_) => match translate_code(e, *l) {
                            Ok(de) => Ok(DStmt::SetThroughField(*f, *g, de)),
                            Err(r) => Err(r),
                        },
                        None => Err(Refusal::NoField(*g, *l)),
                    },
                    Some(_) => Err(Refusal::Syntax(*l)),
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::WriteParam(p, *l)),
            },
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::PushField(f, e, l) => push_field(*f, e, *l, ps, sd),
        Stmt::PopField(f, l) => match self_param(ps) {
            Some((p, t)) => match t {
                Ty::ThisMut(k) => match field_ty(sd, k, *f) {
                    Some(Ty::Seq(_, _)) => Ok(DStmt::SetField(*f, DExpr::PopBack(Box::new(DExpr::Field(Box::new(DExpr::After), *f))))),
                    Some(_) => Err(Refusal::Syntax(*l)),
                    None => Err(Refusal::NoField(*f, *l)),
                },
                _ => Err(Refusal::WriteParam(p, *l)),
            },
            None => Err(Refusal::Syntax(*l)),
        },
        Stmt::PushBack(v, e, l) => push_back(*v, e, *l, all, env, ps, sd),
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
        Expr::Back(a) => has_result(a),
        Expr::Either(a, _) => has_result(a),
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
        Stmt::PushBack(_, e, _) => unmove(e).1,
        Stmt::PushField(_, e, _) => unmove(e).1,
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

pub fn moved_params(ps: &Params, ms: &Names) -> (r: List<(u32, DTy)>)
    ensures
        r == spec_moved_params(*ps, *ms),
    decreases ps,
{
    match ps {
        List::Nil => List::Nil,
        List::Cons((n, t), rest) => match t {
            Ty::Own(s) => if has(ms, *n) {
                List::Cons((*n, DTy::Opt(*s)), Box::new(moved_params(rest, ms)))
            } else {
                moved_params(rest, ms)
            },
            Ty::Vec(s) => List::Cons((*n, DTy::Seq(*s)), Box::new(moved_params(rest, ms))),
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
        List::Cons((n, t), rest) => if (matches!(t, Ty::Own(_)) && has(ms, *n)) || matches!(t, Ty::Vec(_)) {
            kept_params(rest, ms)
        } else {
            List::Cons((*n, *t), Box::new(kept_params(rest, ms)))
        },
    }
}

pub fn param_locals(mp: &List<(u32, DTy)>, line: u32, tail: DStmts) -> (r: DStmts)
    ensures
        r == spec_param_locals(*mp, line, tail),
    decreases mp,
{
    match mp {
        List::Nil => tail,
        List::Cons((n, dt), rest) => List::Cons((Box::new(DStmt::Local(*n, *dt, DExpr::Var(*n))), line), Box::new(param_locals(rest, line, tail))),
    }
}

pub fn param_block(mp: &List<(u32, DTy)>, line: u32, body: DStmts) -> (r: DStmts)
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
        DExpr::Back(x0) => DExpr::Back(Box::new(copy_dexpr(x0))),
        DExpr::PopBack(x0) => DExpr::PopBack(Box::new(copy_dexpr(x0))),
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

pub fn pure_value(body: &DStmts, all: &Fns, sd: &Structs) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_value(*body, *all, *sd),
    decreases body,
{
    match body {
        List::Cons((s, _), rest) => match &**s {
            DStmt::Return(d) => match &**rest {
                List::Nil => Some(copy_dexpr(d)),
                _ => None,
            },
            DStmt::ReturnCall(k, da) => match &**rest {
                List::Nil => if inline(all, *k, sd) {
                    Some(DExpr::FCall(*k, Box::new(copy_dargs(da))))
                } else {
                    None
                },
                _ => None,
            },
            DStmt::Apply(f, da) => match pure_value(rest, all, sd) {
                Some(e) => Some(DExpr::Lemma(*f, Box::new(copy_dargs(da)), Box::new(e))),
                None => None,
            },
            DStmt::Local(n, dt, d) => match pure_value(rest, all, sd) {
                Some(e) => Some(DExpr::Let(*n, *dt, Box::new(copy_dexpr(d)), Box::new(e))),
                None => None,
            },
            DStmt::LocalCall(n, dt, k, da) => if inline(all, *k, sd) {
                match pure_value(rest, all, sd) {
                    Some(e) => Some(DExpr::Let(*n, *dt, Box::new(DExpr::FCall(*k, Box::new(copy_dargs(da)))), Box::new(e))),
                    None => None,
                }
            } else {
                None
            },
            DStmt::If(c, t, f) => match pure_value(t, all, sd) {
                Some(a) => {
                    let b = match &**f {
                        List::Nil => pure_value(rest, all, sd),
                        _ => match &**rest {
                            List::Nil => pure_value(f, all, sd),
                            _ => None,
                        },
                    };
                    match b {
                        Some(b) => Some(DExpr::Ite(Box::new(copy_dexpr(c)), Box::new(a), Box::new(b))),
                        None => None,
                    }
                },
                None => None,
            },
            _ => None,
        },
        List::Nil => None,
    }
}

pub fn pure_body(ps: &Params, body: &DStmts, all: &Fns, sd: &Structs, stat: bool) -> (r: Option<DExpr>)
    ensures
        r == spec_pure_body(*ps, *body, *all, *sd, stat),
{
    if (this_param(ps).is_some() || stat) && !mutates(ps) {
        pure_value(body, all, sd)
    } else {
        None
    }
}

pub fn result_line(cs: &Conds) -> (r: Option<u32>)
    ensures
        r == spec_result_line(*cs),
    decreases cs,
{
    match cs {
        List::Nil => None,
        List::Cons((k, e, l, _), rest) => match e {
            Expr::Bin(BinOp::Eq, a, b) => if *k == CondKind::Ensures && matches!(**a, Expr::Result) && !has_result(b) {
                Some(*l)
            } else {
                result_line(rest)
            },
            _ => result_line(rest),
        },
    }
}

pub fn ens_kind(f: &Function) -> (r: bool)
    ensures
        r == spec_ens_kind(*f),
{
    f.ret == Ty::Bool && this_param(&f.params).is_some() && !mutates(&f.params) && !f.trusted && !const_virtual(f)
        && result_line(&f.conds).is_some()
}

pub fn eq_result_at(ens: &DConds, l: u32) -> (r: Option<DExpr>)
    ensures
        r == spec_eq_result_at(*ens, l),
    decreases ens,
{
    match ens {
        List::Nil => None,
        List::Cons((d, dl), rest) => if *dl == l {
            match d {
                DExpr::Bin(BinOp::Eq, a, b) => if matches!(**a, DExpr::Result) {
                    Some(copy_dexpr(b))
                } else {
                    None
                },
                _ => None,
            }
        } else {
            eq_result_at(rest, l)
        },
    }
}

pub fn member_fn(f: &Function, ens: &DConds, body: &DStmts, all: &Fns, sd: &Structs) -> (r: Option<DExpr>)
    ensures
        r == spec_member_fn(*f, *ens, *body, *all, *sd),
{
    match pure_body(&f.params, body, all, sd, static_key(sd, f.name)) {
        Some(d) => Some(d),
        None => if ens_kind(f) {
            match result_line(&f.conds) {
                Some(l) => eq_result_at(ens, l),
                None => None,
            }
        } else {
            None
        },
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
                Ok((_, ens, _, body)) => match member_fn(f, &ens, &body, all, sd) {
                    Some(_) => Some((f.ret, copy(&f.params))),
                    None => None,
                },
                Err(_) => None,
            }
        } else {
            match translate_stmts(&f.body, all, &f.params, &f.params, sd) {
                Ok(body) => match pure_body(&f.params, &body, all, sd, static_key(sd, f.name)) {
                    Some(_) => Some((f.ret, copy(&f.params))),
                    None => if ens_kind(f) {
                        Some((f.ret, copy(&f.params)))
                    } else {
                        None
                    },
                },
                Err(_) => None,
            }
        },
        None => None,
    }
}

pub fn member_mark(all: &Fns, key: u32, sd: &Structs, strict: bool) -> (r: Option<(Ty, Params)>)
    ensures
        r == spec_member_mark(*all, key, *sd, strict),
{
    if find(all, key).is_none() {
        Some((Ty::Other(key), List::Nil))
    } else {
        pure_ret(all, key, sd, strict)
    }
}

pub fn mark_members(ms: &Members, all: &Fns, sd: &Structs, strict: bool) -> (r: Members)
    ensures
        r == spec_mark_members(*ms, *all, *sd, strict),
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((*n, (*key, member_mark(all, *key, sd, strict))), Box::new(mark_members(rest, all, sd, strict))),
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
                        let pure = member_fn(f, &ens, &body, all, sd);
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
        List::Cons((n, t), rest) => match if matches!(t, Ty::Opt(Scalar::Struct(_)) | Ty::Ptr(_) | Ty::F64) || (matches!(t, Ty::Own(_)) && !matches!(t, Ty::Own(Scalar::Struct(_)))) { Err(Refusal::Element(line)) } else { field_dty(*t, line) } {
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
pub fn marked(sd: &Structs, all: &Fns) -> (r: Structs)
    ensures
        r == spec_marked(*sd, *all),
{
    let top = top(sd, all);
    let ks = all_members(sd);
    settle(sd, all, top, &ks)
}

pub fn top(t: &Structs, all: &Fns) -> (r: Structs)
    ensures
        r == spec_top(*t, *all),
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((k, (l, fields, ms)), rest) => List::Cons((*k, (*l, copy(fields), top_members(ms, all))), Box::new(top(rest, all))),
    }
}

pub fn top_members(ms: &Members, all: &Fns) -> (r: Members)
    ensures
        r == spec_top_members(*ms, *all),
    decreases ms,
{
    match ms {
        List::Nil => List::Nil,
        List::Cons((n, (key, _)), rest) => List::Cons((*n, (*key, top_mark(all, *key))), Box::new(top_members(rest, all))),
    }
}

pub fn top_mark(all: &Fns, key: u32) -> (r: Option<(Ty, Params)>)
    ensures
        r == spec_top_mark(*all, key),
{
    match find(all, key) {
        Some(f) => Some((f.ret, copy(&f.params))),
        None => Some((Ty::Other(key), List::Nil)),
    }
}

pub fn all_members(t: &Structs) -> (r: Members)
    ensures
        r == spec_all_members(*t),
    decreases t,
{
    match t {
        List::Nil => List::Nil,
        List::Cons((_, (_, _, ms)), rest) => append(copy_members(ms), all_members(rest)),
    }
}

pub fn settle(sd: &Structs, all: &Fns, t: Structs, ks: &Members) -> (r: Structs)
    ensures
        r == spec_settle(*sd, *all, t, *ks),
    decreases ks,
{
    let next = mark(sd, all, &t, true);
    match ks {
        List::Nil => next,
        List::Cons(_, rest) => if same_marks(&next, &t) {
            t
        } else {
            settle(sd, all, next, rest)
        },
    }
}

pub fn same_marks(a: &Structs, b: &Structs) -> (r: bool)
    ensures
        r == spec_same_marks(*a, *b),
    decreases a,
{
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons((_, (_, _, ma)), ra), List::Cons((_, (_, _, mb)), rb)) => same_member_marks(ma, mb) && same_marks(ra, rb),
        _ => false,
    }
}

pub fn same_member_marks(a: &Members, b: &Members) -> (r: bool)
    ensures
        r == spec_same_member_marks(*a, *b),
    decreases a,
{
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons((_, (_, x)), ra), List::Cons((_, (_, y)), rb)) => x.is_some() == y.is_some() && same_member_marks(ra, rb),
        _ => false,
    }
}

pub fn translate_unit(all: &Fns, sd: &Structs) -> (r: Models)
    ensures
        r == spec_unit(*all, *all, spec_marked(*sd, *all)),
{
    let marked = marked(sd, all);
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
    let marked = marked(sd, all);
    upcasts(bases, all, &marked)
}

} // verus!

//! The translator: the contract parser. The summary of the proofs is in `model`.

use super::*;
use vstd::prelude::*;

verus! {

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
    Size(u32),
    Field(u32),
    HasValue,
    Value,
    Empty(u32),
    Back(u32),
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
        Tok::Size(_) | Tok::Field(_) | Tok::HasValue | Tok::Value | Tok::Empty(_) | Tok::Back(_) | Tok::LBracket | Tok::Arrow => true,
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
        // `o.size()`, `o.empty()` and `o.back()` keep the form of a sequence and the call of a member, decision 0200.
        if let Tok::Size(id) = toks[p] {
            a = Expr::Either(Box::new(Expr::Size(Box::new(a))), id);
            assert(!unknown_expr(a)) by {
                reveal_with_fuel(unknown_expr, 2);
            }
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
        } else if let Tok::Empty(id) = toks[p] {
            a = Expr::Either(Box::new(Expr::Empty(Box::new(a))), id);
            assert(!unknown_expr(a)) by {
                reveal_with_fuel(unknown_expr, 2);
            }
            p = p + 1;
        } else if let Tok::Back(id) = toks[p] {
            a = Expr::Either(Box::new(Expr::Back(Box::new(a))), id);
            assert(!unknown_expr(a)) by {
                reveal_with_fuel(unknown_expr, 2);
            }
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

} // verus!

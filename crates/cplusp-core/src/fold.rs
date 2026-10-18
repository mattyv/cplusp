//! The fold of named constants and enumerators in a contract, decisions 0106, 0109 and 0124. The shell gives the tokens of a line
//! with the ids of their names, and the constants, the hidden names, the enums and their enumerators, each by id. The core gives
//! the tokens after the fold. It folds the enumerators first and the constants after.

use crate::model::{BinOp, Tok};
use vstd::prelude::*;

verus! {

/// What the fold reads. `constants` are (name, value) in the order of the file. `reals` are the double constants, (name,
/// negative, m, q) for the value `m / q`, decision 0158. `shadow` are the parameters and locals of the
/// function. `enums` are (name, key). `enumerators` are (key, member) in the order of the enum, so the index of a member is the
/// count of the entries of its key before it.
pub struct Folds {
    pub constants: Vec<(u32, i128)>,
    pub reals: Vec<(u32, bool, u64, u64)>,
    pub shadow: Vec<u32>,
    pub enums: Vec<(u32, u32)>,
    pub enumerators: Vec<(u32, u32)>,
}

// ------------------------------------------------------------------ the names that a quantifier binds

/// The names after a `forall` or `exists` at `at`, parted by commas.
pub open spec fn spec_binders(toks: Seq<Tok>, at: int) -> Seq<u32>
    decreases toks.len() - at,
{
    if 0 <= at < toks.len() && toks[at] is Ident {
        let n = toks[at]->Ident_0;
        if at + 1 < toks.len() && toks[at + 1] == Tok::Comma {
            seq![n] + spec_binders(toks, at + 2)
        } else {
            seq![n]
        }
    } else {
        Seq::empty()
    }
}

/// The names that a quantifier binds in the tokens from `i`.
pub open spec fn spec_bound_from(toks: Seq<Tok>, i: int) -> Seq<u32>
    decreases toks.len() - i,
{
    if i < 0 || i >= toks.len() {
        Seq::empty()
    } else if toks[i] == Tok::Forall || toks[i] == Tok::Exists {
        spec_binders(toks, i + 1) + spec_bound_from(toks, i + 1)
    } else {
        spec_bound_from(toks, i + 1)
    }
}

// ponytail: a name bound by a quantifier hides the constant on the whole line. Upgrade: scope the binder.
pub open spec fn spec_bound(toks: Seq<Tok>) -> Seq<u32> {
    spec_bound_from(toks, 0)
}

// ------------------------------------------------------------------ the tables

/// The number of enums with the name `a`.
pub open spec fn enum_count(enums: Seq<(u32, u32)>, a: u32) -> nat
    decreases enums.len(),
{
    if enums.len() == 0 {
        0
    } else {
        enum_count(enums.drop_last(), a) + if enums.last().0 == a { 1nat } else { 0nat }
    }
}

/// The key of the first enum with the name `a`.
pub open spec fn enum_key(enums: Seq<(u32, u32)>, a: u32) -> Option<u32>
    decreases enums.len(),
{
    if enums.len() == 0 {
        None
    } else if enums[0].0 == a {
        Some(enums[0].1)
    } else {
        enum_key(enums.drop_first(), a)
    }
}

/// The index of the first enumerator `b` of the enum `key`: the count of the entries of `key` before it. `seen` counts the
/// entries of `key` that the list has passed.
pub open spec fn member_index(es: Seq<(u32, u32)>, key: u32, b: u32, seen: nat) -> Option<nat>
    decreases es.len(),
{
    if es.len() == 0 {
        None
    } else if es[0].0 == key && es[0].1 == b {
        Some(seen)
    } else {
        member_index(es.drop_first(), key, b, if es[0].0 == key { seen + 1 } else { seen })
    }
}

/// The value of the first constant with the name `n`.
pub open spec fn const_of(cs: Seq<(u32, i128)>, n: u32) -> Option<i128>
    decreases cs.len(),
{
    if cs.len() == 0 {
        None
    } else if cs[0].0 == n {
        Some(cs[0].1)
    } else {
        const_of(cs.drop_first(), n)
    }
}

// ------------------------------------------------------------------ the fold of enumerators

/// `A::B` at `i` as an enumerator, decision 0109: `A` names one enum of the file, no quantifier binds `A`, and `B` is an enumerator
/// of that enum.
pub open spec fn spec_enum_at(toks: Seq<Tok>, i: int, enums: Seq<(u32, u32)>, es: Seq<(u32, u32)>, bound: Seq<u32>) -> Option<Tok> {
    if 0 <= i && i + 2 < toks.len() && toks[i] is Ident && toks[i + 1] == Tok::ColonColon && toks[i + 2] is Ident {
        let a = toks[i]->Ident_0;
        let b = toks[i + 2]->Ident_0;
        if enum_count(enums, a) == 1 && !bound.contains(a) {
            match enum_key(enums, a) {
                Some(key) => match member_index(es, key, b, 0) {
                    Some(k) => Some(Tok::Enumerator(key, k as u32)),
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

pub open spec fn spec_enums_from(toks: Seq<Tok>, i: int, enums: Seq<(u32, u32)>, es: Seq<(u32, u32)>, bound: Seq<u32>) -> Seq<Tok>
    decreases toks.len() - i,
{
    if i < 0 || i >= toks.len() {
        Seq::empty()
    } else {
        match spec_enum_at(toks, i, enums, es, bound) {
            Some(t) => seq![t] + spec_enums_from(toks, i + 3, enums, es, bound),
            None => seq![toks[i]] + spec_enums_from(toks, i + 1, enums, es, bound),
        }
    }
}

// ------------------------------------------------------------------ the fold of constants

/// A value whose magnitude a u64 holds, decision 0063.
pub open spec fn fits(v: i128) -> bool {
    -(u64::MAX as int) <= v <= u64::MAX
}

/// The tokens of a value: a negative value in parentheses, with its exact magnitude.
pub open spec fn spec_value_toks(v: i128) -> Seq<Tok> {
    if v < 0 {
        seq![Tok::LParen, Tok::Op(BinOp::Sub), Tok::Int((-(v as int)) as u64), Tok::RParen]
    } else {
        seq![Tok::Int(v as u64)]
    }
}

/// The name at `i` can be a constant, decision 0106: no parameter, local or bound name hides it, and no call or `::` stands next
/// to it.
pub open spec fn spec_free_at(toks: Seq<Tok>, i: int, shadow: Seq<u32>, bound: Seq<u32>) -> bool {
    0 <= i < toks.len() && toks[i] is Ident && {
        let n = toks[i]->Ident_0;
        let next_ok = !(i + 1 < toks.len() && (toks[i + 1] == Tok::LParen || toks[i + 1] == Tok::ColonColon));
        let prev_ok = i == 0 || toks[i - 1] != Tok::ColonColon;
        !bound.contains(n) && next_ok && prev_ok && !shadow.contains(n)
    }
}

/// The name at `i` as its value, decision 0106: it is a constant, and it is free at `i`.
pub open spec fn spec_const_at(toks: Seq<Tok>, i: int, cs: Seq<(u32, i128)>, shadow: Seq<u32>, bound: Seq<u32>) -> Option<i128> {
    if 0 <= i < toks.len() && toks[i] is Ident {
        let n = toks[i]->Ident_0;
        if spec_free_at(toks, i, shadow, bound) {
            match const_of(cs, n) {
                Some(v) => if fits(v) { Some(v) } else { None },
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The value of the first double constant with the name `n`.
pub open spec fn real_of(rs: Seq<(u32, bool, u64, u64)>, n: u32) -> Option<(bool, u64, u64)>
    decreases rs.len(),
{
    if rs.len() == 0 {
        None
    } else if rs[0].0 == n {
        Some((rs[0].1, rs[0].2, rs[0].3))
    } else {
        real_of(rs.drop_first(), n)
    }
}

/// The name at `i` as the value of a double constant, decision 0158: it is a double constant, and it is free at `i`.
pub open spec fn spec_real_at(toks: Seq<Tok>, i: int, rs: Seq<(u32, bool, u64, u64)>, shadow: Seq<u32>, bound: Seq<u32>) -> Option<
    (bool, u64, u64),
> {
    if spec_free_at(toks, i, shadow, bound) {
        real_of(rs, toks[i]->Ident_0)
    } else {
        None
    }
}

/// The tokens of a double value: `(m / q)` as two decimals, which is the real quotient, decision 0154. A negative value has a minus
/// before `m`.
pub open spec fn spec_real_toks(neg: bool, m: u64, q: u64) -> Seq<Tok> {
    if neg {
        seq![Tok::LParen, Tok::Op(BinOp::Sub), Tok::Real(m, 0), Tok::Op(BinOp::Div), Tok::Real(q, 0), Tok::RParen]
    } else {
        seq![Tok::LParen, Tok::Real(m, 0), Tok::Op(BinOp::Div), Tok::Real(q, 0), Tok::RParen]
    }
}

/// An integer constant of a name comes before a double constant of it.
pub open spec fn spec_consts_from(toks: Seq<Tok>, i: int, cs: Seq<(u32, i128)>, rs: Seq<(u32, bool, u64, u64)>, shadow: Seq<u32>, bound: Seq<u32>) -> Seq<Tok>
    decreases toks.len() - i,
{
    if i < 0 || i >= toks.len() {
        Seq::empty()
    } else {
        match spec_const_at(toks, i, cs, shadow, bound) {
            Some(v) => spec_value_toks(v) + spec_consts_from(toks, i + 1, cs, rs, shadow, bound),
            None => match spec_real_at(toks, i, rs, shadow, bound) {
                Some((neg, m, q)) => spec_real_toks(neg, m, q) + spec_consts_from(toks, i + 1, cs, rs, shadow, bound),
                None => seq![toks[i]] + spec_consts_from(toks, i + 1, cs, rs, shadow, bound),
            },
        }
    }
}

/// The fold of a contract line: the enumerators first, then the constants, each with the names that the line binds.
pub open spec fn spec_fold(toks: Seq<Tok>, cs: Seq<(u32, i128)>, rs: Seq<(u32, bool, u64, u64)>, shadow: Seq<u32>, enums: Seq<(u32, u32)>, es: Seq<(u32, u32)>) -> Seq<
    Tok,
> {
    let e = spec_enums_from(toks, 0, enums, es, spec_bound(toks));
    spec_consts_from(e, 0, cs, rs, shadow, spec_bound(e))
}

// ------------------------------------------------------------------ the code

fn contains(v: &Vec<u32>, n: u32) -> (r: bool)
    ensures
        r == v@.contains(n),
{
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != n,
        decreases v.len() - i,
    {
        if v[i] == n {
            return true;
        }
        i += 1;
    }
    false
}

fn binders(toks: &Vec<Tok>, at: usize, out: &mut Vec<u32>)
    requires
        at <= toks.len() + 1,
    ensures
        final(out)@ == old(out)@ + spec_binders(toks@, at as int),
    decreases toks.len() + 1 - at,
{
    if at < toks.len() {
        if let Tok::Ident(n) = toks[at] {
            out.push(n);
            if at + 1 < toks.len() && toks[at + 1] == Tok::Comma {
                let ghost mid = out@;
                binders(toks, at + 2, out);
                proof {
                    assert(final(out)@ =~= old(out)@ + spec_binders(toks@, at as int));
                }
            } else {
                proof {
                    assert(out@ =~= old(out)@ + spec_binders(toks@, at as int));
                }
            }
            return;
        }
    }
    proof {
        assert(old(out)@ + spec_binders(toks@, at as int) =~= old(out)@);
    }
}

fn bound(toks: &Vec<Tok>) -> (r: Vec<u32>)
    ensures
        r@ == spec_bound(toks@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < toks.len()
        invariant
            i <= toks.len(),
            out@ + spec_bound_from(toks@, i as int) == spec_bound(toks@),
        decreases toks.len() - i,
    {
        let ghost before = out@;
        if toks[i] == Tok::Forall || toks[i] == Tok::Exists {
            binders(toks, i + 1, &mut out);
            proof {
                assert(before + spec_bound_from(toks@, i as int) =~= out@ + spec_bound_from(toks@, i + 1));
            }
        }
        i += 1;
    }
    proof {
        assert(out@ + spec_bound_from(toks@, i as int) =~= out@);
    }
    out
}

fn enum_count_exec(enums: &Vec<(u32, u32)>, a: u32) -> (r: u64)
    ensures
        r as nat == enum_count(enums@, a),
{
    let mut c: u64 = 0;
    let mut i = 0;
    while i < enums.len()
        invariant
            i <= enums.len(),
            c as nat == enum_count(enums@.subrange(0, i as int), a),
            c <= i,
        decreases enums.len() - i,
    {
        proof {
            assert(enums@.subrange(0, i + 1).drop_last() =~= enums@.subrange(0, i as int));
        }
        if enums[i].0 == a {
            c = c + 1;
        }
        i += 1;
    }
    proof {
        assert(enums@.subrange(0, i as int) =~= enums@);
    }
    c
}

fn enum_key_exec(enums: &Vec<(u32, u32)>, a: u32) -> (r: Option<u32>)
    ensures
        r == enum_key(enums@, a),
{
    let mut i = 0;
    proof {
        assert(enums@.subrange(0, enums.len() as int) =~= enums@);
    }
    while i < enums.len()
        invariant
            i <= enums.len(),
            enum_key(enums@, a) == enum_key(enums@.subrange(i as int, enums.len() as int), a),
        decreases enums.len() - i,
    {
        proof {
            assert(enums@.subrange(i as int, enums.len() as int).drop_first() =~= enums@.subrange(i + 1, enums.len() as int));
        }
        if enums[i].0 == a {
            return Some(enums[i].1);
        }
        i += 1;
    }
    None
}

fn member_index_exec(es: &Vec<(u32, u32)>, key: u32, b: u32) -> (r: Option<usize>)
    ensures
        match (r, member_index(es@, key, b, 0)) {
            (Some(x), Some(y)) => x as nat == y,
            (None, None) => true,
            _ => false,
        },
{
    let mut seen: usize = 0;
    let mut i = 0;
    proof {
        assert(es@.subrange(0, es.len() as int) =~= es@);
    }
    while i < es.len()
        invariant
            i <= es.len(),
            seen <= i,
            member_index(es@, key, b, 0) == member_index(es@.subrange(i as int, es.len() as int), key, b, seen as nat),
        decreases es.len() - i,
    {
        proof {
            assert(es@.subrange(i as int, es.len() as int).drop_first() =~= es@.subrange(i + 1, es.len() as int));
        }
        if es[i].0 == key && es[i].1 == b {
            return Some(seen);
        }
        if es[i].0 == key {
            seen = seen + 1;
        }
        i += 1;
    }
    None
}

fn const_of_exec(cs: &Vec<(u32, i128)>, n: u32) -> (r: Option<i128>)
    ensures
        r == const_of(cs@, n),
{
    let mut i = 0;
    proof {
        assert(cs@.subrange(0, cs.len() as int) =~= cs@);
    }
    while i < cs.len()
        invariant
            i <= cs.len(),
            const_of(cs@, n) == const_of(cs@.subrange(i as int, cs.len() as int), n),
        decreases cs.len() - i,
    {
        proof {
            assert(cs@.subrange(i as int, cs.len() as int).drop_first() =~= cs@.subrange(i + 1, cs.len() as int));
        }
        if cs[i].0 == n {
            return Some(cs[i].1);
        }
        i += 1;
    }
    None
}

fn real_of_exec(rs: &Vec<(u32, bool, u64, u64)>, n: u32) -> (r: Option<(bool, u64, u64)>)
    ensures
        r == real_of(rs@, n),
{
    let mut i = 0;
    proof {
        assert(rs@.subrange(0, rs.len() as int) =~= rs@);
    }
    while i < rs.len()
        invariant
            i <= rs.len(),
            real_of(rs@, n) == real_of(rs@.subrange(i as int, rs.len() as int), n),
        decreases rs.len() - i,
    {
        proof {
            assert(rs@.subrange(i as int, rs.len() as int).drop_first() =~= rs@.subrange(i + 1, rs.len() as int));
        }
        if rs[i].0 == n {
            return Some((rs[i].1, rs[i].2, rs[i].3));
        }
        i += 1;
    }
    None
}

fn enum_at(toks: &Vec<Tok>, i: usize, t: &Folds, bound: &Vec<u32>) -> (r: Option<Tok>)
    requires
        i < toks.len(),
    ensures
        r == spec_enum_at(toks@, i as int, t.enums@, t.enumerators@, bound@),
{
    if toks.len() - i > 2 {
        if let (Tok::Ident(a), Tok::ColonColon, Tok::Ident(b)) = (toks[i], toks[i + 1], toks[i + 2]) {
            if enum_count_exec(&t.enums, a) == 1 && !contains(bound, a) {
                if let Some(key) = enum_key_exec(&t.enums, a) {
                    if let Some(k) = member_index_exec(&t.enumerators, key, b) {
                        return Some(Tok::Enumerator(key, k as u32));
                    }
                }
            }
        }
    }
    None
}

fn free_at(toks: &Vec<Tok>, i: usize, t: &Folds, bound: &Vec<u32>) -> (r: bool)
    requires
        i < toks.len(),
    ensures
        r == spec_free_at(toks@, i as int, t.shadow@, bound@),
{
    if let Tok::Ident(n) = toks[i] {
        let next_ok = !(i + 1 < toks.len() && (toks[i + 1] == Tok::LParen || toks[i + 1] == Tok::ColonColon));
        let prev_ok = i == 0 || toks[i - 1] != Tok::ColonColon;
        !contains(bound, n) && next_ok && prev_ok && !contains(&t.shadow, n)
    } else {
        false
    }
}

fn const_at(toks: &Vec<Tok>, i: usize, t: &Folds, bound: &Vec<u32>) -> (r: Option<i128>)
    requires
        i < toks.len(),
    ensures
        r == spec_const_at(toks@, i as int, t.constants@, t.shadow@, bound@),
{
    if let Tok::Ident(n) = toks[i] {
        if free_at(toks, i, t, bound) {
            if let Some(v) = const_of_exec(&t.constants, n) {
                if -(u64::MAX as i128) <= v && v <= u64::MAX as i128 {
                    return Some(v);
                }
            }
        }
    }
    None
}

fn real_at(toks: &Vec<Tok>, i: usize, t: &Folds, bound: &Vec<u32>) -> (r: Option<(bool, u64, u64)>)
    requires
        i < toks.len(),
    ensures
        r == spec_real_at(toks@, i as int, t.reals@, t.shadow@, bound@),
{
    if let Tok::Ident(n) = toks[i] {
        if free_at(toks, i, t, bound) {
            return real_of_exec(&t.reals, n);
        }
    }
    None
}

fn enums_pass(toks: &Vec<Tok>, t: &Folds) -> (r: Vec<Tok>)
    ensures
        r@ == spec_enums_from(toks@, 0, t.enums@, t.enumerators@, spec_bound(toks@)),
{
    let b = bound(toks);
    let mut out: Vec<Tok> = Vec::new();
    let mut i: usize = 0;
    while i < toks.len()
        invariant
            i <= toks.len() + 2,
            b@ == spec_bound(toks@),
            out@ + spec_enums_from(toks@, i as int, t.enums@, t.enumerators@, b@) == spec_enums_from(
                toks@,
                0,
                t.enums@,
                t.enumerators@,
                b@,
            ),
        decreases toks.len() + 2 - i,
    {
        let ghost before = out@;
        match enum_at(toks, i, t, &b) {
            Some(x) => {
                out.push(x);
                proof {
                    assert(before + spec_enums_from(toks@, i as int, t.enums@, t.enumerators@, b@) =~= out@ + spec_enums_from(
                        toks@,
                        i + 3,
                        t.enums@,
                        t.enumerators@,
                        b@,
                    ));
                }
                i = i + 3;
            },
            None => {
                out.push(toks[i]);
                proof {
                    assert(before + spec_enums_from(toks@, i as int, t.enums@, t.enumerators@, b@) =~= out@ + spec_enums_from(
                        toks@,
                        i + 1,
                        t.enums@,
                        t.enumerators@,
                        b@,
                    ));
                }
                i = i + 1;
            },
        }
    }
    proof {
        assert(out@ + spec_enums_from(toks@, i as int, t.enums@, t.enumerators@, b@) =~= out@);
    }
    out
}

fn consts_pass(toks: &Vec<Tok>, t: &Folds) -> (r: Vec<Tok>)
    ensures
        r@ == spec_consts_from(toks@, 0, t.constants@, t.reals@, t.shadow@, spec_bound(toks@)),
{
    let b = bound(toks);
    let mut out: Vec<Tok> = Vec::new();
    let mut i: usize = 0;
    while i < toks.len()
        invariant
            i <= toks.len(),
            b@ == spec_bound(toks@),
            out@ + spec_consts_from(toks@, i as int, t.constants@, t.reals@, t.shadow@, b@) == spec_consts_from(
                toks@,
                0,
                t.constants@,
                t.reals@,
                t.shadow@,
                b@,
            ),
        decreases toks.len() - i,
    {
        let ghost before = out@;
        match const_at(toks, i, t, &b) {
            Some(v) => {
                if v < 0 {
                    let m: u64 = (-v) as u64;
                    out.push(Tok::LParen);
                    out.push(Tok::Op(BinOp::Sub));
                    out.push(Tok::Int(m));
                    out.push(Tok::RParen);
                } else {
                    out.push(Tok::Int(v as u64));
                }
                proof {
                    assert(before + spec_consts_from(toks@, i as int, t.constants@, t.reals@, t.shadow@, b@) =~= out@ + spec_consts_from(
                        toks@,
                        i + 1,
                        t.constants@,
                        t.reals@,
                        t.shadow@,
                        b@,
                    ));
                }
            },
            None => match real_at(toks, i, t, &b) {
                Some((neg, m, q)) => {
                    out.push(Tok::LParen);
                    if neg {
                        out.push(Tok::Op(BinOp::Sub));
                    }
                    out.push(Tok::Real(m, 0));
                    out.push(Tok::Op(BinOp::Div));
                    out.push(Tok::Real(q, 0));
                    out.push(Tok::RParen);
                    proof {
                        assert(before + spec_consts_from(toks@, i as int, t.constants@, t.reals@, t.shadow@, b@) =~= out@ + spec_consts_from(
                            toks@,
                            i + 1,
                            t.constants@,
                            t.reals@,
                            t.shadow@,
                            b@,
                        ));
                    }
                },
                None => {
                out.push(toks[i]);
                proof {
                    assert(before + spec_consts_from(toks@, i as int, t.constants@, t.reals@, t.shadow@, b@) =~= out@ + spec_consts_from(
                        toks@,
                        i + 1,
                        t.constants@,
                        t.reals@,
                        t.shadow@,
                        b@,
                    ));
                }
                },
            },
        }
        i = i + 1;
    }
    proof {
        assert(out@ + spec_consts_from(toks@, i as int, t.constants@, t.reals@, t.shadow@, b@) =~= out@);
    }
    out
}

/// The fold of a contract line, decisions 0106, 0109 and 0124.
pub fn fold(toks: &Vec<Tok>, t: &Folds) -> (r: Vec<Tok>)
    ensures
        r@ == spec_fold(toks@, t.constants@, t.reals@, t.shadow@, t.enums@, t.enumerators@),
{
    let e = enums_pass(toks, t);
    consts_pass(&e, t)
}

} // verus!

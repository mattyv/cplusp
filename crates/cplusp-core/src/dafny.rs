//! The reader of the output of Dafny, decisions 0068, 0069, 0079, 0080, 0083 and 0127. The shell gives the output as bytes. The
//! core reads the summary, the error lines with their related lines and the warning lines, and judges them with the verdict of
//! decision 0077. It proves that `Proved` needs a clean summary, no error line and no axiom in the text, `judge`.

#[allow(unused_imports)]
use crate::verdict::*;
use vstd::prelude::*;

verus! {

/// A summary for a file that Dafny cannot resolve or cannot parse, decision 0080.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Unread {
    Resolve,
    Parse,
}

/// What Dafny printed. `summary` is the first line with the shape of a summary: verified items, errors and time-outs. `errors`
/// and `warnings` are (line of the Dafny text, start, end of the message). `related` is (index of its error, line). `trigger`
/// marks each warning about a missing trigger, decision 0079.
pub struct Reading {
    pub summary: Option<(u64, u64, u64)>,
    pub unread: Option<Unread>,
    pub errors: Vec<(usize, usize, usize)>,
    pub related: Vec<(usize, usize)>,
    pub warnings: Vec<(usize, usize, usize)>,
    pub trigger: Vec<bool>,
}

pub ghost struct SReading {
    pub summary: Option<((u64, u64, u64), Option<Unread>)>,
    pub errors: Seq<(usize, usize, usize)>,
    pub related: Seq<(usize, usize)>,
    pub warnings: Seq<(usize, usize, usize)>,
    pub trigger: Seq<bool>,
}

impl Reading {
    pub open spec fn sview(&self) -> SReading {
        SReading {
            summary: match self.summary { Some(c) => Some((c, self.unread)), None => None },
            errors: self.errors@,
            related: self.related@,
            warnings: self.warnings@,
            trigger: self.trigger@,
        }
    }
}

// ------------------------------------------------------------------ bytes and lines

pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// ASCII white space, as `char::is_whitespace` reads it.
pub open spec fn is_ws(c: u8) -> bool {
    c == 0x20 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13
}

/// `w` stands at `k`, inside the end `e`.
pub open spec fn at(t: Seq<u8>, k: int, e: int, w: Seq<u8>) -> bool {
    0 <= k && k + w.len() <= e && e <= t.len() && t.subrange(k, k + w.len()) == w
}

/// The first place from `k` where `w` stands, inside the end `e`.
pub open spec fn find(t: Seq<u8>, k: int, e: int, w: Seq<u8>) -> Option<int>
    decreases e + 1 - k,
{
    if k < 0 || k + w.len() > e {
        None
    } else if at(t, k, e, w) {
        Some(k)
    } else {
        find(t, k + 1, e, w)
    }
}

proof fn lemma_find(t: Seq<u8>, k: int, e: int, w: Seq<u8>)
    ensures
        find(t, k, e, w) matches Some(x) ==> k <= x && x + w.len() <= e && at(t, x, e, w),
    decreases e + 1 - k,
{
    if !(k < 0 || k + w.len() > e) && !at(t, k, e, w) {
        lemma_find(t, k + 1, e, w);
    }
}

proof fn lemma_rfind(t: Seq<u8>, s: int, e: int, c: u8)
    ensures
        rfind(t, s, e, c) matches Some(x) ==> s <= x < e,
    decreases e - s,
{
    if e > s && t[e - 1] != c {
        lemma_rfind(t, s, e - 1, c);
    }
}

/// The last place before `e` and from `s` that holds the byte `c`.
pub open spec fn rfind(t: Seq<u8>, s: int, e: int, c: u8) -> Option<int>
    decreases e - s,
{
    if e <= s {
        None
    } else if t[e - 1] == c {
        Some(e - 1)
    } else {
        rfind(t, s, e - 1, c)
    }
}

/// The value of decimal digits.
pub open spec fn dec(t: Seq<u8>, s: int, e: int) -> nat
    decreases e - s,
{
    if e <= s {
        0
    } else {
        dec(t, s, e - 1) * 10 + (t[e - 1] - 0x30) as nat
    }
}

/// A number as Rust parses it: an optional `+`, then one or more digits, at most `max`.
pub open spec fn parse(t: Seq<u8>, s: int, e: int, max: nat) -> Option<nat> {
    let a = if s < e && t[s] == 0x2b { s + 1 } else { s };
    if a < e && (forall|k: int| a <= k < e ==> is_digit(#[trigger] t[k])) && dec(t, a, e) <= max {
        Some(dec(t, a, e))
    } else {
        None
    }
}

/// The end of the line that starts at `i`: the next line feed, or the end of the text.
pub open spec fn line_end(t: Seq<u8>, i: int) -> int
    decreases t.len() - i,
{
    if i >= t.len() || i < 0 {
        t.len() as int
    } else if t[i] == 10 {
        i
    } else {
        line_end(t, i + 1)
    }
}

/// The end of the text of the line from `s` to `e`: a carriage return before the line feed is no part of it, as in `str::lines`.
pub open spec fn text_end(t: Seq<u8>, s: int, e: int) -> int {
    if e < t.len() && s < e && t[e - 1] == 13 { e - 1 } else { e }
}

/// The end after ASCII white space is trimmed.
pub open spec fn trim_end(t: Seq<u8>, s: int, e: int) -> int
    decreases e - s,
{
    if e > s && is_ws(t[e - 1]) {
        trim_end(t, s, e - 1)
    } else {
        e
    }
}

// ------------------------------------------------------------------ one line

/// `PATH(L,C): KIND: MESSAGE` on the line from `s` to `e`: the line number and the start of the message. The first `: KIND: `
/// splits the line, as `split_once` does.
pub open spec fn spec_at(t: Seq<u8>, s: int, e: int, p: Seq<u8>) -> Option<(nat, int)> {
    match find(t, s, e, p) {
        None => None,
        Some(k) => if k > s && t[k - 1] == 0x29 {
            match rfind(t, s, k - 1, 0x28) {
                None => None,
                Some(q) => match find(t, q + 1, k - 1, seq![0x2cu8]) {
                    None => None,
                    Some(c) => match parse(t, q + 1, c, usize::MAX as nat) {
                        Some(n) => Some((n, k + p.len())),
                        None => None,
                    },
                },
            }
        } else {
            None
        },
    }
}

pub open spec fn error_mark() -> Seq<u8> {
    b": Error: "@
}

pub open spec fn related_mark() -> Seq<u8> {
    b": Related location: "@
}

pub open spec fn warning_mark() -> Seq<u8> {
    b": Warning: "@
}

pub open spec fn trigger_text() -> Seq<u8> {
    b"Could not find a trigger for this quantifier"@
}

pub open spec fn summary_head() -> Seq<u8> {
    b"Dafny program verifier finished with "@
}

/// One part of a summary, `N WORD`: the count when the word after the first space is one of `w1` and `w2`.
pub open spec fn spec_part(t: Seq<u8>, s: int, e: int, w1: Seq<u8>, w2: Seq<u8>) -> Option<nat> {
    match find(t, s, e, seq![0x20u8]) {
        None => None,
        Some(sp) => {
            let w = t.subrange(sp + 1, e);
            if w == w1 || w == w2 {
                parse(t, s, sp, u64::MAX as nat)
            } else {
                None
            }
        },
    }
}

/// The counts of a summary line from `s` to `e`, decisions 0068 and 0080.
pub open spec fn spec_counts(t: Seq<u8>, s: int, e: int) -> Option<((u64, u64, u64), Option<Unread>)> {
    let first = match find(t, s, e, seq![0x20u8]) {
        Some(sp) => if at(t, sp + 1, e, b"resolution/type error"@) && find(t, sp + 1, e, b" detected in "@) is Some {
            Some((sp, Unread::Resolve))
        } else if at(t, sp + 1, e, b"parse error"@) && find(t, sp + 1, e, b" detected in "@) is Some {
            Some((sp, Unread::Parse))
        } else {
            None
        },
        None => None,
    };
    match first {
        Some((sp, kind)) => match parse(t, s, sp, u64::MAX as nat) {
            Some(n) => Some(((0, n as u64, 0), Some(kind))),
            None => None,
        },
        None => if at(t, s, e, summary_head()) {
            let a = s + summary_head().len();
            let z = trim_end(t, a, e);
            match find(t, a, z, b", "@) {
                None => None,
                Some(k1) => match find(t, k1 + 2, z, b", "@) {
                    None => match (spec_part(t, a, k1, b"verified"@, b"verified"@), spec_part(t, k1 + 2, z, b"error"@, b"errors"@)) {
                        (Some(v), Some(x)) => Some(((v as u64, x as u64, 0), None)),
                        _ => None,
                    },
                    Some(k2) => if find(t, k2 + 2, z, b", "@) is Some {
                        None
                    } else {
                        match (
                            spec_part(t, a, k1, b"verified"@, b"verified"@),
                            spec_part(t, k1 + 2, k2, b"error"@, b"errors"@),
                            spec_part(t, k2 + 2, z, b"time out"@, b"time outs"@),
                        ) {
                            (Some(v), Some(x), Some(o)) => Some(((v as u64, x as u64, o as u64), None)),
                            _ => None,
                        }
                    },
                },
            }
        } else {
            None
        },
    }
}

// ------------------------------------------------------------------ the text

/// The reading after one more line, from `s` to `e`.
#[verifier::opaque]
pub open spec fn spec_line(r: SReading, t: Seq<u8>, s: int, e: int) -> SReading {
    let summary = if r.summary is Some { r.summary } else { spec_counts(t, s, e) };
    let (errors, related) = match spec_at(t, s, e, error_mark()) {
        Some((n, m)) => (r.errors.push((n as usize, m as usize, e as usize)), r.related),
        None => match spec_at(t, s, e, related_mark()) {
            Some((n, _)) => if r.errors.len() > 0 {
                (r.errors, r.related.push(((r.errors.len() - 1) as usize, n as usize)))
            } else {
                (r.errors, r.related)
            },
            None => (r.errors, r.related),
        },
    };
    let (warnings, trigger) = match spec_at(t, s, e, warning_mark()) {
        Some((n, m)) => (r.warnings.push((n as usize, m as usize, e as usize)), r.trigger.push(at(t, m, e, trigger_text()))),
        None => (r.warnings, r.trigger),
    };
    SReading { summary, errors, related, warnings, trigger }
}

/// The reading of the lines from `i` to the end, after the reading `r`.
pub open spec fn spec_read_from(r: SReading, t: Seq<u8>, i: int) -> SReading
    decreases t.len() + 1 - i,
    via lemma_read_decreases
{
    if i < 0 || i >= t.len() {
        r
    } else {
        let e = line_end(t, i);
        let r2 = spec_line(r, t, i, text_end(t, i, e));
        spec_read_from(r2, t, e + 1)
    }
}

#[via_fn]
proof fn lemma_read_decreases(r: SReading, t: Seq<u8>, i: int) {
    if 0 <= i < t.len() {
        lemma_line_end(t, i);
    }
}

proof fn lemma_line_end(t: Seq<u8>, i: int)
    requires
        0 <= i <= t.len(),
    ensures
        i <= line_end(t, i) <= t.len(),
        line_end(t, i) < t.len() ==> t[line_end(t, i)] == 10,
    decreases t.len() - i,
{
    if i < t.len() && t[i] != 10 {
        lemma_line_end(t, i + 1);
    }
}

pub open spec fn spec_empty() -> SReading {
    SReading { summary: None, errors: Seq::empty(), related: Seq::empty(), warnings: Seq::empty(), trigger: Seq::empty() }
}

/// The reading of the output of Dafny, decision 0127.
pub open spec fn spec_read(t: Seq<u8>) -> SReading {
    spec_read_from(spec_empty(), t, 0)
}

// ------------------------------------------------------------------ the judge

/// A line of the Dafny text in the companion file, which takes the indexes from `lo` to `hi`. The line after the last also counts,
/// decision 0083.
pub open spec fn in_companion(n: usize, lo: usize, hi: usize) -> bool {
    lo < hi && ((n >= 1 && lo <= n - 1 < hi) || n == hi + 1)
}

/// A warning on a line of the companion file is an axiom, except a missing trigger, decision 0079.
pub open spec fn axiom_count(ws: Seq<(usize, usize, usize)>, tr: Seq<bool>, lo: usize, hi: usize) -> nat
    decreases ws.len(),
{
    if ws.len() == 0 || tr.len() < ws.len() {
        0
    } else {
        let w = ws.last();
        axiom_count(ws.drop_last(), tr.drop_last(), lo, hi) + if w.0 >= 1 && lo <= w.0 - 1 < hi && !tr[ws.len() - 1] { 1nat } else { 0nat }
    }
}

/// The summary that the verdict reads. A parse error is the author's only when each error is in the companion file, decision 0083.
pub open spec fn spec_summary(r: SReading, lo: usize, hi: usize) -> Option<(u64, u64, u64)> {
    match r.summary {
        None => None,
        Some((c, u)) => if u == Some(Unread::Parse) && !(r.errors.len() > 0 && forall|k: int|
            0 <= k < r.errors.len() ==> in_companion(#[trigger] r.errors[k].0, lo, hi)) {
            None
        } else {
            Some(c)
        },
    }
}

pub open spec fn spec_judge(r: SReading, exit_ok: bool, refused: bool, methods: usize, lo: usize, hi: usize) -> Verdict {
    spec_verdict(exit_ok, spec_summary(r, lo, hi), r.errors.len() as usize, refused, axiom_count(r.warnings, r.trigger, lo, hi) as usize, methods)
}

// ------------------------------------------------------------------ the code

fn at_exec(t: &Vec<u8>, k: usize, e: usize, w: &[u8]) -> (r: bool)
    requires
        e <= t.len(),
    ensures
        r == at(t@, k as int, e as int, w@),
{
    if k > e || w.len() > e - k {
        return false;
    }
    let mut i = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            k + w.len() <= e <= t.len(),
            forall|j: int| 0 <= j < i ==> t@[k + j] == w@[j],
        decreases w.len() - i,
    {
        if t[k + i] != w[i] {
            proof {
                assert(t@.subrange(k as int, k + w.len())[i as int] != w@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(t@.subrange(k as int, k + w.len()) =~= w@);
    }
    true
}

fn find_exec(t: &Vec<u8>, k: usize, e: usize, w: &[u8]) -> (r: Option<usize>)
    requires
        e <= t.len(),
    ensures
        match r {
            Some(x) => find(t@, k as int, e as int, w@) == Some(x as int) && k <= x && x + w@.len() <= e,
            None => find(t@, k as int, e as int, w@) is None,
        },
{
    proof {
        lemma_find(t@, k as int, e as int, w@);
    }
    if w.len() == 0 {
        if k <= e {
            proof {
                assert(t@.subrange(k as int, k as int) =~= w@);
            }
            return Some(k);
        }
        return None;
    }
    if k > e {
        return None;
    }
    let mut i = k;
    while w.len() <= e - i
        invariant
            k <= i <= e,
            e <= t.len(),
            w.len() >= 1,
            find(t@, k as int, e as int, w@) == find(t@, i as int, e as int, w@),
        decreases e - i,
    {
        if at_exec(t, i, e, w) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn rfind_exec(t: &Vec<u8>, s: usize, e: usize, c: u8) -> (r: Option<usize>)
    requires
        e <= t.len(),
    ensures
        match r {
            Some(x) => rfind(t@, s as int, e as int, c) == Some(x as int) && s <= x < e,
            None => rfind(t@, s as int, e as int, c) is None,
        },
{
    proof {
        lemma_rfind(t@, s as int, e as int, c);
    }
    let mut j = e;
    while j > s
        invariant
            j <= e <= t.len(),
            rfind(t@, s as int, e as int, c) == rfind(t@, s as int, j as int, c),
        decreases j,
    {
        if t[j - 1] == c {
            return Some(j - 1);
        }
        j -= 1;
    }
    None
}

proof fn lemma_dec_grows(t: Seq<u8>, s: int, e: int, m: int)
    requires
        s <= m <= e,
        forall|k: int| s <= k < e ==> is_digit(#[trigger] t[k]),
    ensures
        dec(t, s, m) <= dec(t, s, e),
    decreases e - m,
{
    if m < e {
        lemma_dec_grows(t, s, e, m + 1);
    }
}

/// A number as Rust parses it, at most `max`.
fn parse_exec(t: &Vec<u8>, s: usize, e: usize, max: u64) -> (r: Option<u64>)
    requires
        s <= e <= t.len(),
    ensures
        match r {
            Some(v) => parse(t@, s as int, e as int, max as nat) == Some(v as nat),
            None => parse(t@, s as int, e as int, max as nat) is None,
        },
{
    let a = if s < e && t[s] == 0x2b { s + 1 } else { s };
    if a >= e {
        return None;
    }
    let mut k = a;
    while k < e
        invariant
            a <= k <= e <= t.len(),
            a as int == (if (s as int) < (e as int) && t@[s as int] == 0x2b { s + 1 } else { s as int }),
            forall|j: int| a <= j < k ==> is_digit(#[trigger] t@[j]),
        decreases e - k,
    {
        if !(0x30 <= t[k] && t[k] <= 0x39) {
            proof {
                assert(!is_digit(t@[k as int]));
                assert(!(forall|j: int| a <= j < e ==> is_digit(#[trigger] t@[j])));
                assert(a as int == (if (s as int) < (e as int) && t@[s as int] == 0x2b { s + 1 } else { s as int }));
            }
            return None;
        }
        k += 1;
    }
    let mut v: u64 = 0;
    let mut i = a;
    while i < e
        invariant
            a <= i <= e <= t.len(),
            a as int == (if (s as int) < (e as int) && t@[s as int] == 0x2b { s + 1 } else { s as int }),
            forall|j: int| a <= j < e ==> is_digit(#[trigger] t@[j]),
            v as nat == dec(t@, a as int, i as int),
            v <= max,
        decreases e - i,
    {
        let d = (t[i] - 0x30) as u64;
        proof {
            lemma_dec_grows(t@, a as int, e as int, i + 1);
        }
        let n: u128 = (v as u128) * 10 + (d as u128);
        proof {
            assert(dec(t@, a as int, i + 1) == dec(t@, a as int, i as int) * 10 + (t@[i as int] - 0x30) as nat);
            assert(n == dec(t@, a as int, i + 1));
        }
        if n > max as u128 {
            proof {
                assert(dec(t@, a as int, e as int) > max);
                assert(a as int == (if (s as int) < (e as int) && t@[s as int] == 0x2b { s + 1 } else { s as int }));
            }
            return None;
        }
        v = n as u64;
        i += 1;
    }
    Some(v)
}

fn line_end_exec(t: &Vec<u8>, i: usize) -> (r: usize)
    requires
        i <= t.len(),
    ensures
        r == line_end(t@, i as int),
{
    let mut k = i;
    while k < t.len() && t[k] != 10
        invariant
            i <= k <= t.len(),
            line_end(t@, k as int) == line_end(t@, i as int),
        decreases t.len() - k,
    {
        k += 1;
    }
    k
}

fn trim_end_exec(t: &Vec<u8>, s: usize, e: usize) -> (r: usize)
    requires
        e <= t.len(),
    ensures
        r == trim_end(t@, s as int, e as int),
        r <= e,
{
    let mut z = e;
    while z > s && {
        let c = t[z - 1];
        c == 0x20 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13
    }
        invariant
            z <= e <= t.len(),
            trim_end(t@, s as int, z as int) == trim_end(t@, s as int, e as int),
        decreases z,
    {
        z -= 1;
    }
    z
}

fn at_kind(t: &Vec<u8>, s: usize, e: usize, p: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        s <= e <= t.len(),
    ensures
        match (r, spec_at(t@, s as int, e as int, p@)) {
            (Some((n, m)), Some((n2, m2))) => n as nat == n2 && m as int == m2,
            (None, None) => true,
            _ => false,
        },
{
    proof {
        assert(seq![0x2cu8] =~= [0x2cu8]@);
    }
    match find_exec(t, s, e, p) {
        None => None,
        Some(k) => {
            if k > s && t[k - 1] == 0x29 {
                match rfind_exec(t, s, k - 1, 0x28) {
                    None => None,
                    Some(q) => match find_exec(t, q + 1, k - 1, &[0x2c]) {
                        None => None,
                        Some(c) => {
                            proof {
                                assert(seq![0x2cu8] =~= [0x2cu8]@);
                            }
                            match parse_exec(t, q + 1, c, usize::MAX as u64) {
                                Some(n) => Some((n as usize, k + p.len())),
                                None => None,
                            }
                        },
                    },
                }
            } else {
                None
            }
        },
    }
}

fn part(t: &Vec<u8>, s: usize, e: usize, w1: &[u8], w2: &[u8]) -> (r: Option<u64>)
    requires
        s <= e <= t.len(),
    ensures
        match r {
            Some(v) => spec_part(t@, s as int, e as int, w1@, w2@) == Some(v as nat),
            None => spec_part(t@, s as int, e as int, w1@, w2@) is None,
        },
{
    proof {
        assert(seq![0x20u8] =~= [0x20u8]@);
    }
    match find_exec(t, s, e, &[0x20]) {
        None => None,
        Some(sp) => {
            if (e - (sp + 1) == w1.len() && at_exec(t, sp + 1, e, w1)) || (e - (sp + 1) == w2.len() && at_exec(t, sp + 1, e, w2)) {
                proof {
                    assert(t@.subrange(sp + 1, e as int) == w1@ ==> t@.subrange(sp + 1, sp + 1 + w1@.len()) =~= t@.subrange(sp + 1, e as int));
                }
                parse_exec(t, s, sp, u64::MAX)
            } else {
                proof {
                    if t@.subrange(sp + 1, e as int) == w1@ {
                        assert(t@.subrange(sp + 1, e as int).len() == w1@.len());
                        assert(t@.subrange(sp + 1, sp + 1 + w1@.len()) =~= t@.subrange(sp + 1, e as int));
                    }
                    if t@.subrange(sp + 1, e as int) == w2@ {
                        assert(t@.subrange(sp + 1, e as int).len() == w2@.len());
                        assert(t@.subrange(sp + 1, sp + 1 + w2@.len()) =~= t@.subrange(sp + 1, e as int));
                    }
                }
                None
            }
        },
    }
}

fn counts(t: &Vec<u8>, s: usize, e: usize) -> (r: Option<((u64, u64, u64), Option<Unread>)>)
    requires
        s <= e <= t.len(),
    ensures
        r == spec_counts(t@, s as int, e as int),
{
    proof {
        assert(seq![0x20u8] =~= [0x20u8]@);
    }
    let first: Option<(usize, Unread)> = match find_exec(t, s, e, &[0x20]) {
        Some(sp) => {
            if at_exec(t, sp + 1, e, b"resolution/type error") && find_exec(t, sp + 1, e, b" detected in ").is_some() {
                Some((sp, Unread::Resolve))
            } else if at_exec(t, sp + 1, e, b"parse error") && find_exec(t, sp + 1, e, b" detected in ").is_some() {
                Some((sp, Unread::Parse))
            } else {
                None
            }
        },
        None => None,
    };
    match first {
        Some((sp, kind)) => match parse_exec(t, s, sp, u64::MAX) {
            Some(n) => Some(((0, n, 0), Some(kind))),
            None => None,
        },
        None => {
            if !at_exec(t, s, e, b"Dafny program verifier finished with ") {
                return None;
            }
            let a = s + 37;
            let z = trim_end_exec(t, a, e);
            proof {
                assert(summary_head().len() == 37);
            }
            match find_exec(t, a, z, b", ") {
                None => None,
                Some(k1) => match find_exec(t, k1 + 2, z, b", ") {
                    None => match (part(t, a, k1, b"verified", b"verified"), part(t, k1 + 2, z, b"error", b"errors")) {
                        (Some(v), Some(x)) => Some(((v, x, 0), None)),
                        _ => None,
                    },
                    Some(k2) => {
                        if find_exec(t, k2 + 2, z, b", ").is_some() {
                            None
                        } else {
                            match (part(t, a, k1, b"verified", b"verified"), part(t, k1 + 2, k2, b"error", b"errors"), part(t, k2 + 2, z, b"time out", b"time outs")) {
                                (Some(v), Some(x), Some(o)) => Some(((v, x, o), None)),
                                _ => None,
                            }
                        }
                    },
                },
            }
        },
    }
}

fn read_line(
    summary: &mut Option<((u64, u64, u64), Option<Unread>)>,
    errors: &mut Vec<(usize, usize, usize)>,
    related: &mut Vec<(usize, usize)>,
    warnings: &mut Vec<(usize, usize, usize)>,
    trigger: &mut Vec<bool>,
    t: &Vec<u8>,
    s: usize,
    z: usize,
)
    requires
        s <= z <= t.len(),
    ensures
        (SReading { summary: *final(summary), errors: final(errors)@, related: final(related)@, warnings: final(warnings)@, trigger: final(trigger)@ })
            == spec_line(
            SReading { summary: *old(summary), errors: old(errors)@, related: old(related)@, warnings: old(warnings)@, trigger: old(trigger)@ },
            t@,
            s as int,
            z as int,
        ),
{
    reveal(spec_line);
    if summary.is_none() {
        *summary = counts(t, s, z);
    }
    match at_kind(t, s, z, b": Error: ") {
        Some((n, m)) => errors.push((n, m, z)),
        None => match at_kind(t, s, z, b": Related location: ") {
            Some((n, _)) => {
                if errors.len() > 0 {
                    related.push((errors.len() - 1, n));
                }
            },
            None => {},
        },
    }
    match at_kind(t, s, z, b": Warning: ") {
        Some((n, m)) => {
            proof {
                lemma_find(t@, s as int, z as int, warning_mark());
            }
            warnings.push((n, m, z));
            trigger.push(at_exec(t, m, z, b"Could not find a trigger for this quantifier"));
        },
        None => {},
    }
}

/// The output of Dafny as facts, decision 0127.
pub fn read_dafny(t: &Vec<u8>) -> (r: Reading)
    ensures
        r.sview() == spec_read(t@),
{
    let mut summary: Option<((u64, u64, u64), Option<Unread>)> = None;
    let mut errors: Vec<(usize, usize, usize)> = Vec::new();
    let mut related: Vec<(usize, usize)> = Vec::new();
    let mut warnings: Vec<(usize, usize, usize)> = Vec::new();
    let mut trigger: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            spec_read_from(SReading { summary, errors: errors@, related: related@, warnings: warnings@, trigger: trigger@ }, t@, i as int) == spec_read(t@),
        decreases t.len() - i,
    {
        let e = line_end_exec(t, i);
        proof {
            lemma_line_end(t@, i as int);
        }
        let z = if e < t.len() && i < e && t[e - 1] == 13 { e - 1 } else { e };
        let ghost before = SReading { summary, errors: errors@, related: related@, warnings: warnings@, trigger: trigger@ };
        read_line(&mut summary, &mut errors, &mut related, &mut warnings, &mut trigger, t, i, z);
        let ghost after = SReading { summary, errors: errors@, related: related@, warnings: warnings@, trigger: trigger@ };
        proof {
            assert(spec_read_from(before, t@, i as int) == spec_read_from(after, t@, e + 1));
        }
        if e >= t.len() {
            proof {
                assert(spec_read_from(after, t@, e + 1) == after);
                assert(spec_read_from(after, t@, t.len() as int) == after);
            }
            i = t.len();
        } else {
            i = e + 1;
        }
    }
    let r = Reading {
        summary: match summary { Some((c, _)) => Some(c), None => None },
        unread: match summary { Some((_, u)) => u, None => None },
        errors,
        related,
        warnings,
        trigger,
    };
    proof {
        assert(r.sview() == spec_read_from(SReading { summary, errors: errors@, related: related@, warnings: warnings@, trigger: trigger@ }, t@, i as int));
    }
    r
}

fn in_companion_exec(n: usize, lo: usize, hi: usize) -> (b: bool)
    requires
        hi < usize::MAX,
    ensures
        b == in_companion(n, lo, hi),
{
    lo < hi && ((n >= 1 && lo <= n - 1 && n - 1 < hi) || n == hi + 1)
}

/// The verdict of a run, decision 0127. It is `Proved` only when the text has a clean summary that counts each method, no error
/// line and no axiom on the companion file, Dafny exits with success and the translator refuses nothing.
pub fn judge(r: &Reading, exit_ok: bool, refused: bool, methods: usize, lo: usize, hi: usize) -> (v: Verdict)
    requires
        hi < usize::MAX,
        r.trigger@.len() == r.warnings@.len(),
    ensures
        v == spec_judge(r.sview(), exit_ok, refused, methods, lo, hi),
        v == Verdict::Proved <==> ({
            let s = spec_summary(r.sview(), lo, hi);
            &&& exit_ok
            &&& s is Some && s.unwrap().1 == 0 && s.unwrap().2 == 0 && s.unwrap().0 >= methods as u64
            &&& r.errors@.len() == 0
            &&& !refused
            &&& axiom_count(r.warnings@, r.trigger@, lo, hi) == 0
        }),
{
    let mut all = true;
    let mut k = 0;
    while k < r.errors.len()
        invariant
            k <= r.errors.len(),
            hi < usize::MAX,
            all == (forall|j: int| 0 <= j < k ==> in_companion(#[trigger] r.errors@[j].0, lo, hi)),
        decreases r.errors.len() - k,
    {
        if !in_companion_exec(r.errors[k].0, lo, hi) {
            all = false;
        }
        k += 1;
    }
    let all = all && r.errors.len() > 0;
    let summary = if r.unread == Some(Unread::Parse) && !all { None } else { r.summary };
    proof {
        assert(summary == spec_summary(r.sview(), lo, hi));
    }
    let mut axioms: usize = 0;
    let mut w = 0;
    while w < r.warnings.len()
        invariant
            w <= r.warnings.len(),
            r.trigger@.len() == r.warnings@.len(),
            axioms as nat == axiom_count(r.warnings@.subrange(0, w as int), r.trigger@.subrange(0, w as int), lo, hi),
            axioms <= w,
        decreases r.warnings.len() - w,
    {
        let (n, _, _) = r.warnings[w];
        proof {
            assert(r.warnings@.subrange(0, w + 1).drop_last() =~= r.warnings@.subrange(0, w as int));
            assert(r.trigger@.subrange(0, w + 1).drop_last() =~= r.trigger@.subrange(0, w as int));
        }
        if n >= 1 && lo <= n - 1 && n - 1 < hi && !r.trigger[w] {
            axioms += 1;
        }
        w += 1;
    }
    proof {
        assert(r.warnings@.subrange(0, w as int) =~= r.warnings@);
        assert(r.trigger@.subrange(0, w as int) =~= r.trigger@);
    }
    verdict(exit_ok, summary, r.errors.len(), refused, axioms, methods)
}

} // verus!

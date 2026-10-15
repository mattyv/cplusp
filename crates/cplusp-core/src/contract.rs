//! The lexer of a contract line, decisions 0082, 0106 and 0124. The shell gives the bytes of the line. The core gives the tokens,
//! each with its span. It proves that the lexer drops no text except ASCII white space, `lex_contract`, and that a number is the
//! value of its digits in its base, `spec_number`.

use crate::model::{BinOp, Tok};
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ the result

/// Why a number cannot be read, decision 0082. `NoDigits` is `0x` with no hex digit after it. `Octal` is a decimal number with a
/// leading 0 and more digits. `Suffix` is a suffix other than u, l, ul, lu, ll, ull and llu, in any case, with its length in the
/// number without separators. `TooBig` is a value above the largest u64.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum NumberFault {
    NoDigits,
    Octal,
    Suffix(usize),
    TooBig,
}

/// What a token is. A name has a mark when a `(` follows it. A field is `.` and a name, and its span holds the `.`. A
/// character that a contract cannot hold is `BadChar`, with all of its bytes.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum LexKind {
    Name(bool),
    Field,
    Fixed(Tok),
    Int(u64),
    Real(u64, u32),
    BadNumber(NumberFault),
    BadChar,
}

/// A token and its span in the bytes of the line.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub struct Lexeme {
    pub start: usize,
    pub end: usize,
    pub kind: LexKind,
}

// ------------------------------------------------------------------ classes of bytes

/// ASCII white space, as `char::is_whitespace` reads it: space, tab, line feed, vertical tab, form feed, carriage return.
pub open spec fn is_ws(c: u8) -> bool {
    c == 0x20 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13
}

pub open spec fn is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5a) || (0x61 <= c <= 0x7a)
}

pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

pub open spec fn is_alnum(c: u8) -> bool {
    is_alpha(c) || is_digit(c)
}

pub open spec fn is_hex(c: u8) -> bool {
    is_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

/// A byte that starts a name: a letter or `_`.
pub open spec fn name_start(c: u8) -> bool {
    is_alpha(c) || c == 0x5f
}

/// A byte inside a name: a letter, a digit or `_`.
pub open spec fn name_byte(c: u8) -> bool {
    is_alnum(c) || c == 0x5f
}

// ------------------------------------------------------------------ runs

/// The end of the run of name bytes from `j`.
pub open spec fn name_end(t: Seq<u8>, j: int) -> int
    decreases t.len() - j,
{
    if 0 <= j < t.len() && name_byte(t[j]) {
        name_end(t, j + 1)
    } else {
        j
    }
}

/// The end of a number from `j`: letters and digits, and a `'` between two of them.
pub open spec fn num_end(t: Seq<u8>, j: int) -> int
    decreases t.len() - j,
{
    if 0 <= j < t.len() && (is_alnum(t[j]) || (t[j] == 0x27 && j + 1 < t.len() && is_alnum(t[j + 1]))) {
        num_end(t, j + 1)
    } else {
        j
    }
}

/// The first byte from `j` that is no white space.
pub open spec fn skip_ws(t: Seq<u8>, j: int) -> int
    decreases t.len() - j,
{
    if 0 <= j < t.len() && is_ws(t[j]) {
        skip_ws(t, j + 1)
    } else {
        j
    }
}

proof fn lemma_runs(t: Seq<u8>, j: int)
    requires
        0 <= j <= t.len(),
    ensures
        j <= name_end(t, j) <= t.len(),
        j <= num_end(t, j) <= t.len(),
        j <= skip_ws(t, j) <= t.len(),
    decreases t.len() - j,
{
    if j < t.len() {
        lemma_runs(t, j + 1);
    }
}

/// `w` stands at `i`.
pub open spec fn at(t: Seq<u8>, i: int, w: Seq<u8>) -> bool {
    0 <= i && i + w.len() <= t.len() && t.subrange(i, i + w.len()) == w
}

/// A `(` follows the place `j`, after white space.
pub open spec fn paren_after(t: Seq<u8>, j: int) -> bool {
    let k = skip_ws(t, j);
    k < t.len() && t[k] == 0x28
}

// ------------------------------------------------------------------ numbers

/// The bytes without the separators `'`.
pub open spec fn strip(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if s.last() == 0x27 {
        strip(s.drop_last())
    } else {
        strip(s.drop_last()).push(s.last())
    }
}

/// The value of a digit in base 10 or 16.
pub open spec fn digit(c: u8) -> nat {
    if is_digit(c) {
        (c - 0x30) as nat
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as nat
    } else {
        (c - 0x61 + 10) as nat
    }
}

/// The value of digits in a base.
pub open spec fn value(s: Seq<u8>, base: nat) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        value(s.drop_last(), base) * base + digit(s.last())
    }
}

/// The length of the run of digits of the base at the start of `s`.
pub open spec fn digits_len(s: Seq<u8>, hex: bool) -> nat
    decreases s.len(),
{
    if s.len() > 0 && (if hex { is_hex(s[0]) } else { is_digit(s[0]) }) {
        1 + digits_len(s.drop_first(), hex)
    } else {
        0
    }
}

pub open spec fn lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5a { (c + 0x20) as u8 } else { c }
}

/// `s` is `w` in any case.
pub open spec fn ieq(s: Seq<u8>, w: Seq<u8>) -> bool {
    s.len() == w.len() && forall|k: int| 0 <= k < s.len() ==> lower(s[k]) == w[k]
}

/// A suffix of a C++ integer: u, l, ul, lu, ll, ull or llu, in any case, or none.
pub open spec fn suffix_ok(s: Seq<u8>) -> bool {
    s.len() == 0 || ieq(s, b"u"@) || ieq(s, b"l"@) || ieq(s, b"ul"@) || ieq(s, b"lu"@) || ieq(s, b"ll"@) || ieq(s, b"ull"@)
        || ieq(s, b"llu"@)
}

/// A number, decision 0082. The digits are those of its base after `0x` or `0X`, without separators. The rest is the suffix. A
/// leading 0 with more digits is octal in C++ and is refused.
pub open spec fn spec_number(w: Seq<u8>) -> LexKind {
    let hex = w.len() >= 2 && w[0] == 0x30 && (w[1] == 0x78 || w[1] == 0x58);
    let body = if hex { w.subrange(2, w.len() as int) } else { w };
    let n = digits_len(body, hex);
    let digits = body.subrange(0, n as int);
    let suffix = body.subrange(n as int, body.len() as int);
    if n == 0 {
        LexKind::BadNumber(NumberFault::NoDigits)
    } else if !hex && n > 1 && body[0] == 0x30 {
        LexKind::BadNumber(NumberFault::Octal)
    } else if !suffix_ok(suffix) {
        LexKind::BadNumber(NumberFault::Suffix(suffix.len() as usize))
    } else if value(digits, if hex { 16 } else { 10 }) > u64::MAX {
        LexKind::BadNumber(NumberFault::TooBig)
    } else {
        LexKind::Int(value(digits, if hex { 16 } else { 10 }) as u64)
    }
}

/// A decimal with a point, decision 0150: digits, `.` and digits, with no separator, suffix or exponent. `w` is the part before
/// the point and `f` the part after it. Its value is the digits of both parts, over ten to the count of the digits in `f`.
pub open spec fn spec_real_lit(w: Seq<u8>, f: Seq<u8>) -> LexKind {
    let all = w + f;
    if digits_len(all, false) != all.len() {
        LexKind::BadNumber(NumberFault::Suffix((all.len() - digits_len(all, false)) as usize))
    } else if w.len() > 1 && w[0] == 0x30 {
        LexKind::BadNumber(NumberFault::Octal)
    } else if f.len() > 19 || value(all, 10) > u64::MAX {
        LexKind::BadNumber(NumberFault::TooBig)
    } else {
        LexKind::Real(value(all, 10) as u64, f.len() as u32)
    }
}

// ------------------------------------------------------------------ one token

/// The length of a UTF-8 character from its first byte. A byte that starts none is one byte.
pub open spec fn char_len(c: u8) -> int {
    if 0xc0 <= c <= 0xdf {
        2
    } else if 0xe0 <= c <= 0xef {
        3
    } else if 0xf0 <= c <= 0xf7 {
        4
    } else {
        1
    }
}

/// An operator and its text, longest first.
pub open spec fn spec_op(t: Seq<u8>, i: int) -> Option<(int, BinOp)> {
    if at(t, i, b"==>"@) {
        Some((3, BinOp::Implies))
    } else if at(t, i, b"&&"@) {
        Some((2, BinOp::And))
    } else if at(t, i, b"||"@) {
        Some((2, BinOp::Or))
    } else if at(t, i, b"<="@) {
        Some((2, BinOp::Le))
    } else if at(t, i, b">="@) {
        Some((2, BinOp::Ge))
    } else if at(t, i, b"=="@) {
        Some((2, BinOp::Eq))
    } else if at(t, i, b"!="@) {
        Some((2, BinOp::Ne))
    } else if at(t, i, b"<"@) {
        Some((1, BinOp::Lt))
    } else if at(t, i, b">"@) {
        Some((1, BinOp::Gt))
    } else if at(t, i, b"+"@) {
        Some((1, BinOp::Add))
    } else if at(t, i, b"-"@) {
        Some((1, BinOp::Sub))
    } else if at(t, i, b"*"@) {
        Some((1, BinOp::Mul))
    } else if at(t, i, b"/"@) {
        Some((1, BinOp::Div))
    } else if at(t, i, b"%"@) {
        Some((1, BinOp::Rem))
    } else {
        None
    }
}

/// A token of one byte.
pub open spec fn spec_single(c: u8) -> Option<Tok> {
    if c == 0x21 {
        Some(Tok::Bang)
    } else if c == 0x28 {
        Some(Tok::LParen)
    } else if c == 0x29 {
        Some(Tok::RParen)
    } else if c == 0x5b {
        Some(Tok::LBracket)
    } else if c == 0x5d {
        Some(Tok::RBracket)
    } else if c == 0x2c {
        Some(Tok::Comma)
    } else if c == 0x3f {
        Some(Tok::Question)
    } else if c == 0x3a {
        Some(Tok::Colon)
    } else {
        None
    }
}

/// A name, or a word of the grammar. `old` is a word only before `(`, decision 0057.
pub open spec fn spec_word(t: Seq<u8>, i: int, e: int) -> LexKind {
    let w = t.subrange(i, e);
    if w == b"result"@ {
        LexKind::Fixed(Tok::Result)
    } else if w == b"old"@ && paren_after(t, e) {
        LexKind::Fixed(Tok::Old)
    } else if w == b"forall"@ {
        LexKind::Fixed(Tok::Forall)
    } else if w == b"exists"@ {
        LexKind::Fixed(Tok::Exists)
    } else if w == b"true"@ {
        LexKind::Fixed(Tok::Bool(true))
    } else if w == b"false"@ {
        LexKind::Fixed(Tok::Bool(false))
    } else if w == b"nullptr"@ {
        LexKind::Fixed(Tok::Nullptr)
    } else {
        LexKind::Name(paren_after(t, e))
    }
}

/// The token at `i`, a byte that is no white space: its end and its kind, in the order of decision 0124.
pub open spec fn spec_token(t: Seq<u8>, i: int) -> (int, LexKind) {
    let c = t[i];
    if at(t, i, b"std::isfinite"@) && !(i + 13 < t.len() && name_byte(t[i + 13])) {
        (i + 13, LexKind::Fixed(Tok::IsFinite))
    } else if name_start(c) {
        let e = name_end(t, i + 1);
        (e, spec_word(t, i, e))
    } else if is_digit(c) {
        let e = num_end(t, i + 1);
        if e + 1 < t.len() && t[e] == 0x2e && is_digit(t[e + 1]) {
            let f = num_end(t, e + 1);
            (f, spec_real_lit(t.subrange(i, e), t.subrange(e + 1, f)))
        } else {
            (e, spec_number(strip(t.subrange(i, e))))
        }
    } else if at(t, i, b".size()"@) {
        (i + 7, LexKind::Fixed(Tok::Size))
    } else if at(t, i, b".empty()"@) {
        (i + 8, LexKind::Fixed(Tok::Empty))
    } else if at(t, i, b".has_value()"@) {
        (i + 12, LexKind::Fixed(Tok::HasValue))
    } else if at(t, i, b".value()"@) {
        (i + 8, LexKind::Fixed(Tok::Value))
    } else if at(t, i, b".."@) {
        (i + 2, LexKind::Fixed(Tok::DotDot))
    } else if at(t, i, b"::"@) {
        (i + 2, LexKind::Fixed(Tok::ColonColon))
    } else if at(t, i, b"->"@) {
        (i + 2, LexKind::Fixed(Tok::Arrow))
    } else if c == 0x2e && i + 1 < t.len() && name_start(t[i + 1]) {
        (name_end(t, i + 1), LexKind::Field)
    } else if c == 0x27 && i + 2 < t.len() && 0x20 <= t[i + 1] <= 0x7e && t[i + 1] != 0x27 && t[i + 1] != 0x5c && t[i + 2] == 0x27 {
        (i + 3, LexKind::Int(t[i + 1] as u64))
    } else if let Some((n, o)) = spec_op(t, i) {
        (i + n, LexKind::Fixed(Tok::Op(o)))
    } else if let Some(k) = spec_single(c) {
        (i + 1, LexKind::Fixed(k))
    } else {
        (if i + char_len(c) <= t.len() { i + char_len(c) } else { t.len() as int }, LexKind::BadChar)
    }
}

proof fn lemma_token(t: Seq<u8>, i: int)
    requires
        0 <= i < t.len(),
    ensures
        i < spec_token(t, i).0 <= t.len(),
{
    lemma_runs(t, i + 1);
    let e = num_end(t, i + 1);
    if e + 1 < t.len() {
        lemma_runs(t, e + 1);
    }
    if let Some((n, o)) = spec_op(t, i) {
        assert(1 <= n <= 3);
    }
}

// ------------------------------------------------------------------ the line

/// The tokens from `i` to the end of the line.
pub open spec fn spec_lex_from(t: Seq<u8>, i: int) -> Seq<Lexeme>
    decreases t.len() - i,
    via lemma_lex_decreases
{
    if i < 0 || i >= t.len() {
        Seq::empty()
    } else if is_ws(t[i]) {
        spec_lex_from(t, i + 1)
    } else {
        let (e, k) = spec_token(t, i);
        seq![Lexeme { start: i as usize, end: e as usize, kind: k }] + spec_lex_from(t, e)
    }
}

#[via_fn]
proof fn lemma_lex_decreases(t: Seq<u8>, i: int) {
    if 0 <= i < t.len() && !is_ws(t[i]) {
        lemma_token(t, i);
    }
}

/// The tokens of the line, decision 0124.
pub open spec fn spec_lex(t: Seq<u8>) -> Seq<Lexeme> {
    spec_lex_from(t, 0)
}

/// The spans of the tokens are in order from `from`, and each byte outside them is white space.
pub open spec fn covers(t: Seq<u8>, toks: Seq<Lexeme>, from: int) -> bool
    decreases toks.len(),
{
    if toks.len() == 0 {
        forall|k: int| from <= k < t.len() ==> is_ws(#[trigger] t[k])
    } else {
        &&& from <= toks[0].start < toks[0].end <= t.len()
        &&& forall|k: int| from <= k < toks[0].start ==> is_ws(#[trigger] t[k])
        &&& covers(t, toks.drop_first(), toks[0].end as int)
    }
}

proof fn lemma_covers(t: Seq<u8>, i: int)
    requires
        0 <= i <= t.len(),
        t.len() <= usize::MAX,
    ensures
        covers(t, spec_lex_from(t, i), i),
    decreases t.len() - i,
{
    if i < t.len() {
        if is_ws(t[i]) {
            lemma_covers(t, i + 1);
            let r = spec_lex_from(t, i + 1);
            assert(spec_lex_from(t, i) == r);
            if r.len() > 0 {
                assert(covers(t, r.drop_first(), r[0].end as int));
            }
        } else {
            lemma_token(t, i);
            let (e, k) = spec_token(t, i);
            lemma_covers(t, e);
            let r = spec_lex_from(t, i);
            assert(r.drop_first() =~= spec_lex_from(t, e));
        }
    }
}

// ------------------------------------------------------------------ the code

fn word_is(t: &Vec<u8>, s: usize, e: usize, w: &[u8]) -> (r: bool)
    requires
        s <= e <= t.len(),
    ensures
        r == (t@.subrange(s as int, e as int) == w@),
{
    if e - s != w.len() {
        proof {
            if t@.subrange(s as int, e as int) == w@ {
                assert(t@.subrange(s as int, e as int).len() == w@.len());
            }
        }
        return false;
    }
    let mut i = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            e - s == w.len(),
            s <= e <= t.len(),
            forall|j: int| 0 <= j < i ==> t@[s + j] == w@[j],
        decreases w.len() - i,
    {
        if t[s + i] != w[i] {
            proof {
                assert(t@.subrange(s as int, e as int)[i as int] != w@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(t@.subrange(s as int, e as int) =~= w@);
    }
    true
}

fn at_exec(t: &Vec<u8>, i: usize, w: &[u8]) -> (r: bool)
    requires
        i <= t.len(),
    ensures
        r == at(t@, i as int, w@),
{
    if w.len() > t.len() - i {
        return false;
    }
    word_is(t, i, i + w.len(), w)
}

fn name_end_exec(t: &Vec<u8>, j: usize) -> (r: usize)
    requires
        j <= t.len(),
    ensures
        r == name_end(t@, j as int),
{
    let mut k = j;
    while k < t.len() && {
        let c = t[k];
        (0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || (0x30 <= c && c <= 0x39) || c == 0x5f
    }
        invariant
            j <= k <= t.len(),
            name_end(t@, k as int) == name_end(t@, j as int),
        decreases t.len() - k,
    {
        k += 1;
    }
    k
}

fn num_end_exec(t: &Vec<u8>, j: usize) -> (r: usize)
    requires
        j <= t.len(),
    ensures
        r == num_end(t@, j as int),
{
    let mut k = j;
    while k < t.len() && {
        let c = t[k];
        let alnum = |c: u8| -> (r: bool)
            ensures
                r == is_alnum(c),
            { (0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || (0x30 <= c && c <= 0x39) };
        alnum(c) || (c == 0x27 && k + 1 < t.len() && alnum(t[k + 1]))
    }
        invariant
            j <= k <= t.len(),
            num_end(t@, k as int) == num_end(t@, j as int),
        decreases t.len() - k,
    {
        k += 1;
    }
    k
}

fn skip_ws_exec(t: &Vec<u8>, j: usize) -> (r: usize)
    requires
        j <= t.len(),
    ensures
        r == skip_ws(t@, j as int),
{
    let mut k = j;
    while k < t.len() && {
        let c = t[k];
        c == 0x20 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13
    }
        invariant
            j <= k <= t.len(),
            skip_ws(t@, k as int) == skip_ws(t@, j as int),
        decreases t.len() - k,
    {
        k += 1;
    }
    k
}

fn paren_after_exec(t: &Vec<u8>, j: usize) -> (r: bool)
    requires
        j <= t.len(),
    ensures
        r == paren_after(t@, j as int),
{
    let k = skip_ws_exec(t, j);
    proof {
        lemma_runs(t@, j as int);
    }
    k < t.len() && t[k] == 0x28
}

/// The bytes from `s` to `e` without the separators.
fn strip_exec(t: &Vec<u8>, s: usize, e: usize) -> (r: Vec<u8>)
    requires
        s <= e <= t.len(),
    ensures
        r@ == strip(t@.subrange(s as int, e as int)),
{
    let mut w: Vec<u8> = Vec::new();
    let mut k = s;
    while k < e
        invariant
            s <= k <= e <= t.len(),
            w@ == strip(t@.subrange(s as int, k as int)),
        decreases e - k,
    {
        proof {
            assert(t@.subrange(s as int, k + 1).drop_last() =~= t@.subrange(s as int, k as int));
        }
        if t[k] != 0x27 {
            w.push(t[k]);
        }
        k += 1;
    }
    w
}

fn digits_len_exec(w: &Vec<u8>, from: usize, hex: bool) -> (r: usize)
    requires
        from <= w.len(),
    ensures
        r == digits_len(w@.subrange(from as int, w.len() as int), hex),
        from + r <= w.len(),
{
    let mut k = from;
    while k < w.len() && {
        let c = w[k];
        if hex {
            (0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
        } else {
            0x30 <= c && c <= 0x39
        }
    }
        invariant
            from <= k <= w.len(),
            digits_len(w@.subrange(from as int, w.len() as int), hex) == (k - from) + digits_len(
                w@.subrange(k as int, w.len() as int),
                hex,
            ),
        decreases w.len() - k,
    {
        proof {
            assert(w@.subrange(k as int, w.len() as int).drop_first() =~= w@.subrange(k + 1, w.len() as int));
        }
        k += 1;
    }
    proof {
        if k < w.len() {
            assert(w@.subrange(k as int, w.len() as int)[0] == w@[k as int]);
        }
    }
    k - from
}

proof fn lemma_value_grows(s: Seq<u8>, base: nat, n: nat)
    requires
        n <= s.len(),
        base >= 1,
    ensures
        value(s.subrange(0, n as int), base) <= value(s, base),
    decreases s.len() - n,
{
    if n < s.len() {
        lemma_value_grows(s, base, (n + 1) as nat);
        assert(s.subrange(0, n + 1 as int).drop_last() =~= s.subrange(0, n as int));
        assert(value(s.subrange(0, n as int), base) <= value(s.subrange(0, n as int), base) * base) by (nonlinear_arith)
            requires
                base >= 1,
        ;
    } else {
        assert(s.subrange(0, n as int) =~= s);
    }
}

/// The value of the digits from `s` to `e`, or `None` above the largest u64.
fn value_exec(w: &Vec<u8>, s: usize, e: usize, hex: bool) -> (r: Option<u64>)
    requires
        s <= e <= w.len(),
        forall|k: int| s <= k < e ==> if hex { is_hex(w@[k]) } else { is_digit(w@[k]) },
    ensures
        match r {
            Some(v) => v == value(w@.subrange(s as int, e as int), if hex { 16 } else { 10 }),
            None => value(w@.subrange(s as int, e as int), if hex { 16 } else { 10 }) > u64::MAX,
        },
{
    let base: u64 = if hex { 16 } else { 10 };
    let ghost b: nat = if hex { 16 } else { 10 };
    let mut v: u64 = 0;
    let mut k = s;
    while k < e
        invariant
            s <= k <= e <= w.len(),
            base == b,
            b == (if hex { 16nat } else { 10nat }),
            forall|j: int| s <= j < e ==> if hex { is_hex(w@[j]) } else { is_digit(w@[j]) },
            v == value(w@.subrange(s as int, k as int), b),
        decreases e - k,
    {
        let c = w[k];
        let d: u64 = if 0x30 <= c && c <= 0x39 {
            (c - 0x30) as u64
        } else if 0x41 <= c && c <= 0x46 {
            (c - 0x41 + 10) as u64
        } else {
            (c - 0x61 + 10) as u64
        };
        let ghost next = value(w@.subrange(s as int, k + 1), b);
        proof {
            assert(w@.subrange(s as int, k + 1).drop_last() =~= w@.subrange(s as int, k as int));
            assert(w@.subrange(s as int, k + 1).last() == c);
            assert(d == digit(c));
            assert(next == v * b + d);
            let full = w@.subrange(s as int, e as int);
            lemma_value_grows(full, b, (k + 1 - s) as nat);
            assert(full.subrange(0, k + 1 - s) =~= w@.subrange(s as int, k + 1));
            assert(next <= value(full, b));
        }
        match v.checked_mul(base) {
            None => {
                proof {
                    assert(v * b > u64::MAX);
                    assert(v * b + d >= v * b);
                    assert(value(w@.subrange(s as int, e as int), b) > u64::MAX);
                }
                return None;
            },
            Some(m) => match m.checked_add(d) {
                None => {
                    proof {
                        assert(value(w@.subrange(s as int, e as int), b) > u64::MAX);
                    }
                    return None;
                },
                Some(n) => {
                    v = n;
                },
            },
        }
        k += 1;
    }
    Some(v)
}

fn lower_exec(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if 0x41 <= c && c <= 0x5a {
        c + 0x20
    } else {
        c
    }
}

fn ieq_exec(w: &Vec<u8>, s: usize, e: usize, x: &[u8]) -> (r: bool)
    requires
        s <= e <= w.len(),
    ensures
        r == ieq(w@.subrange(s as int, e as int), x@),
{
    if e - s != x.len() {
        return false;
    }
    let mut k = 0;
    while k < x.len()
        invariant
            k <= x.len(),
            e - s == x.len(),
            s <= e <= w.len(),
            forall|j: int| 0 <= j < k ==> lower(w@[s + j]) == x@[j],
        decreases x.len() - k,
    {
        if lower_exec(w[s + k]) != x[k] {
            return false;
        }
        k += 1;
    }
    true
}

fn suffix_ok_exec(w: &Vec<u8>, s: usize, e: usize) -> (r: bool)
    requires
        s <= e <= w.len(),
    ensures
        r == suffix_ok(w@.subrange(s as int, e as int)),
{
    s == e || ieq_exec(w, s, e, b"u") || ieq_exec(w, s, e, b"l") || ieq_exec(w, s, e, b"ul") || ieq_exec(w, s, e, b"lu") || ieq_exec(
        w,
        s,
        e,
        b"ll",
    ) || ieq_exec(w, s, e, b"ull") || ieq_exec(w, s, e, b"llu")
}

fn number(w: &Vec<u8>) -> (r: LexKind)
    ensures
        r == spec_number(w@),
{
    let hex = w.len() >= 2 && w[0] == 0x30 && (w[1] == 0x78 || w[1] == 0x58);
    let from: usize = if hex { 2 } else { 0 };
    let n = digits_len_exec(w, from, hex);
    let ghost body = if hex { w@.subrange(2, w.len() as int) } else { w@ };
    proof {
        assert(w@.subrange(from as int, w.len() as int) =~= body);
        assert(body.subrange(0, n as int) =~= w@.subrange(from as int, from + n));
        assert(body.subrange(n as int, body.len() as int) =~= w@.subrange(from + n, w.len() as int));
        lemma_digits_are_digits(body, hex);
        assert forall|k: int| from <= k < from + n implies if hex { is_hex(#[trigger] w@[k]) } else { is_digit(w@[k]) } by {
            assert(w@[k] == body[k - from]);
        }
    }
    if n == 0 {
        return LexKind::BadNumber(NumberFault::NoDigits);
    }
    if !hex && n > 1 && w[0] == 0x30 {
        return LexKind::BadNumber(NumberFault::Octal);
    }
    if !suffix_ok_exec(w, from + n, w.len()) {
        return LexKind::BadNumber(NumberFault::Suffix(w.len() - (from + n)));
    }
    match value_exec(w, from, from + n, hex) {
        None => LexKind::BadNumber(NumberFault::TooBig),
        Some(v) => LexKind::Int(v),
    }
}

fn real_lit(t: &Vec<u8>, i: usize, e: usize, f: usize) -> (r: LexKind)
    requires
        i <= e < f <= t.len(),
    ensures
        r == spec_real_lit(t@.subrange(i as int, e as int), t@.subrange(e + 1, f as int)),
{
    let mut w: Vec<u8> = Vec::new();
    let mut k = i;
    while k < e
        invariant
            i <= k <= e < f <= t.len(),
            w@ =~= t@.subrange(i as int, k as int),
        decreases e - k,
    {
        w.push(t[k]);
        k += 1;
    }
    let mut k = e + 1;
    while k < f
        invariant
            e + 1 <= k <= f <= t.len(),
            i <= e,
            w@ =~= t@.subrange(i as int, e as int) + t@.subrange(e + 1, k as int),
        decreases f - k,
    {
        w.push(t[k]);
        k += 1;
    }
    let ghost all = t@.subrange(i as int, e as int) + t@.subrange(e + 1, f as int);
    proof {
        assert(w@ =~= all);
        assert(w@.subrange(0, w.len() as int) =~= all);
        lemma_digits_are_digits(all, false);
    }
    let n = digits_len_exec(&w, 0, false);
    if n != w.len() {
        return LexKind::BadNumber(NumberFault::Suffix(w.len() - n));
    }
    if e - i > 1 && t[i] == 0x30 {
        proof {
            assert(t@.subrange(i as int, e as int)[0] == t@[i as int]);
        }
        return LexKind::BadNumber(NumberFault::Octal);
    }
    proof {
        if e - i > 1 {
            assert(t@.subrange(i as int, e as int)[0] == t@[i as int]);
        }
    }
    if f - e - 1 > 19 {
        return LexKind::BadNumber(NumberFault::TooBig);
    }
    proof {
        assert(w@.subrange(0, w.len() as int) =~= all);
    }
    match value_exec(&w, 0, w.len(), false) {
        None => LexKind::BadNumber(NumberFault::TooBig),
        Some(v) => LexKind::Real(v, (f - e - 1) as u32),
    }
}

proof fn lemma_digits_are_digits(s: Seq<u8>, hex: bool)
    ensures
        digits_len(s, hex) <= s.len(),
        forall|k: int| 0 <= k < digits_len(s, hex) ==> if hex { is_hex(#[trigger] s[k]) } else { is_digit(s[k]) },
    decreases s.len(),
{
    if s.len() > 0 && (if hex { is_hex(s[0]) } else { is_digit(s[0]) }) {
        lemma_digits_are_digits(s.drop_first(), hex);
        assert forall|k: int| 0 <= k < digits_len(s, hex) implies if hex { is_hex(#[trigger] s[k]) } else { is_digit(s[k]) } by {
            if k > 0 {
                assert(s[k] == s.drop_first()[k - 1]);
            }
        }
    }
}

fn op_exec(t: &Vec<u8>, i: usize) -> (r: Option<(usize, BinOp)>)
    requires
        i <= t.len(),
    ensures
        match (r, spec_op(t@, i as int)) {
            (Some((n, o)), Some((m, p))) => n == m && o == p,
            (None, None) => true,
            _ => false,
        },
{
    if at_exec(t, i, b"==>") {
        Some((3, BinOp::Implies))
    } else if at_exec(t, i, b"&&") {
        Some((2, BinOp::And))
    } else if at_exec(t, i, b"||") {
        Some((2, BinOp::Or))
    } else if at_exec(t, i, b"<=") {
        Some((2, BinOp::Le))
    } else if at_exec(t, i, b">=") {
        Some((2, BinOp::Ge))
    } else if at_exec(t, i, b"==") {
        Some((2, BinOp::Eq))
    } else if at_exec(t, i, b"!=") {
        Some((2, BinOp::Ne))
    } else if at_exec(t, i, b"<") {
        Some((1, BinOp::Lt))
    } else if at_exec(t, i, b">") {
        Some((1, BinOp::Gt))
    } else if at_exec(t, i, b"+") {
        Some((1, BinOp::Add))
    } else if at_exec(t, i, b"-") {
        Some((1, BinOp::Sub))
    } else if at_exec(t, i, b"*") {
        Some((1, BinOp::Mul))
    } else if at_exec(t, i, b"/") {
        Some((1, BinOp::Div))
    } else if at_exec(t, i, b"%") {
        Some((1, BinOp::Rem))
    } else {
        None
    }
}

fn single_exec(c: u8) -> (r: Option<Tok>)
    ensures
        r == spec_single(c),
{
    if c == 0x21 {
        Some(Tok::Bang)
    } else if c == 0x28 {
        Some(Tok::LParen)
    } else if c == 0x29 {
        Some(Tok::RParen)
    } else if c == 0x5b {
        Some(Tok::LBracket)
    } else if c == 0x5d {
        Some(Tok::RBracket)
    } else if c == 0x2c {
        Some(Tok::Comma)
    } else if c == 0x3f {
        Some(Tok::Question)
    } else if c == 0x3a {
        Some(Tok::Colon)
    } else {
        None
    }
}

fn word_exec(t: &Vec<u8>, i: usize, e: usize) -> (r: LexKind)
    requires
        i <= e <= t.len(),
    ensures
        r == spec_word(t@, i as int, e as int),
{
    if word_is(t, i, e, b"result") {
        LexKind::Fixed(Tok::Result)
    } else if word_is(t, i, e, b"old") && paren_after_exec(t, e) {
        LexKind::Fixed(Tok::Old)
    } else if word_is(t, i, e, b"forall") {
        LexKind::Fixed(Tok::Forall)
    } else if word_is(t, i, e, b"exists") {
        LexKind::Fixed(Tok::Exists)
    } else if word_is(t, i, e, b"true") {
        LexKind::Fixed(Tok::Bool(true))
    } else if word_is(t, i, e, b"false") {
        LexKind::Fixed(Tok::Bool(false))
    } else if word_is(t, i, e, b"nullptr") {
        LexKind::Fixed(Tok::Nullptr)
    } else {
        LexKind::Name(paren_after_exec(t, e))
    }
}

fn token(t: &Vec<u8>, i: usize) -> (r: (usize, LexKind))
    requires
        i < t.len(),
    ensures
        r.0 == spec_token(t@, i as int).0,
        r.1 == spec_token(t@, i as int).1,
{
    proof {
        lemma_runs(t@, i + 1);
    }
    let c = t[i];
    if at_exec(t, i, b"std::isfinite") && !(t.len() - i > 13 && {
        let d = t[i + 13];
        (0x30 <= d && d <= 0x39) || (0x41 <= d && d <= 0x5a) || (0x61 <= d && d <= 0x7a) || d == 0x5f
    }) {
        (i + 13, LexKind::Fixed(Tok::IsFinite))
    } else if (0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || c == 0x5f {
        let e = name_end_exec(t, i + 1);
        (e, word_exec(t, i, e))
    } else if 0x30 <= c && c <= 0x39 {
        let e = num_end_exec(t, i + 1);
        if e < t.len() && t.len() - e > 1 && t[e] == 0x2e && 0x30 <= t[e + 1] && t[e + 1] <= 0x39 {
            proof {
                lemma_runs(t@, e + 1);
            }
            let f = num_end_exec(t, e + 1);
            (f, real_lit(t, i, e, f))
        } else {
            let w = strip_exec(t, i, e);
            (e, number(&w))
        }
    } else if at_exec(t, i, b".size()") {
        (i + 7, LexKind::Fixed(Tok::Size))
    } else if at_exec(t, i, b".empty()") {
        (i + 8, LexKind::Fixed(Tok::Empty))
    } else if at_exec(t, i, b".has_value()") {
        (i + 12, LexKind::Fixed(Tok::HasValue))
    } else if at_exec(t, i, b".value()") {
        (i + 8, LexKind::Fixed(Tok::Value))
    } else if at_exec(t, i, b"..") {
        (i + 2, LexKind::Fixed(Tok::DotDot))
    } else if at_exec(t, i, b"::") {
        (i + 2, LexKind::Fixed(Tok::ColonColon))
    } else if at_exec(t, i, b"->") {
        (i + 2, LexKind::Fixed(Tok::Arrow))
    } else if c == 0x2e && i + 1 < t.len() && {
        let d = t[i + 1];
        (0x41 <= d && d <= 0x5a) || (0x61 <= d && d <= 0x7a) || d == 0x5f
    } {
        (name_end_exec(t, i + 1), LexKind::Field)
    } else if c == 0x27 && t.len() - i > 2 && 0x20 <= t[i + 1] && t[i + 1] <= 0x7e && t[i + 1] != 0x27 && t[i + 1] != 0x5c && t[i
        + 2] == 0x27 {
        (i + 3, LexKind::Int(t[i + 1] as u64))
    } else if let Some((n, o)) = op_exec(t, i) {
        (i + n, LexKind::Fixed(Tok::Op(o)))
    } else if let Some(k) = single_exec(c) {
        (i + 1, LexKind::Fixed(k))
    } else {
        let n: usize = if 0xc0 <= c && c <= 0xdf {
            2
        } else if 0xe0 <= c && c <= 0xef {
            3
        } else if 0xf0 <= c && c <= 0xf7 {
            4
        } else {
            1
        };
        (if n <= t.len() - i { i + n } else { t.len() }, LexKind::BadChar)
    }
}

/// The tokens of a contract line, decision 0124. The lexer drops no text except ASCII white space.
pub fn lex_contract(t: &Vec<u8>) -> (r: Vec<Lexeme>)
    ensures
        r@ == spec_lex(t@),
        covers(t@, r@, 0),
{
    let mut out: Vec<Lexeme> = Vec::new();
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            out@ + spec_lex_from(t@, i as int) == spec_lex(t@),
        decreases t.len() - i,
    {
        let c = t[i];
        if c == 0x20 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13 {
            i += 1;
        } else {
            proof {
                lemma_token(t@, i as int);
            }
            let (e, k) = token(t, i);
            let ghost before = out@;
            out.push(Lexeme { start: i, end: e, kind: k });
            proof {
                let l = Lexeme { start: i, end: e, kind: k };
                assert(spec_lex_from(t@, i as int) == seq![l] + spec_lex_from(t@, e as int));
                assert(out@ + spec_lex_from(t@, e as int) =~= before + spec_lex_from(t@, i as int));
            }
            i = e;
        }
    }
    proof {
        assert(out@ + spec_lex_from(t@, i as int) =~= out@);
        lemma_covers(t@, 0);
    }
    out
}

} // verus!

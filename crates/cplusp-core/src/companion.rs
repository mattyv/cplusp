//! The scan of the companion file, decisions 0080, 0083 and 0123. The shell gives the bytes of the file. The core gives the
//! refusals and the names that the file declares. The scan has two parts: a lexer that reads the bytes as Dafny reads them and
//! makes tokens, and a rule that reads each token. The core proves that a file passes only when no byte, comment or token breaks
//! the rules, `scan_companion`.

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ the result

/// Why the scan refuses a line. `Char` is a byte that a companion file cannot hold, decision 0083. `Word` is a keyword of Dafny
/// that is not on the short list, decision 0080. `ModelName` is a declared name that the prelude or the model uses, decision 0083.
/// A word is a span of the bytes.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CompanionRefusal {
    Char,
    Word(usize, usize),
    Quote,
    At,
    Attribute,
    ModelName(usize, usize),
    Unclosed,
}

/// The refusals in the order of the scan, each with its line, and the declared names as (start, end, line, lemma). A file with a
/// refusal declares no name.
pub struct CompanionScan {
    pub refusals: Vec<(u32, CompanionRefusal)>,
    pub declared: Vec<(usize, usize, u32, bool)>,
}

// ------------------------------------------------------------------ bytes

/// A byte that a companion file can hold: printable ASCII, a tab, a line feed, or a carriage return before a line feed.
pub open spec fn byte_ok(t: Seq<u8>, i: int) -> bool {
    let c = t[i];
    (0x20 <= c <= 0x7e) || c == 9 || c == 10 || (c == 13 && i + 1 < t.len() && t[i + 1] == 10)
}

/// The line of each refused byte of the first `n` bytes, once for each line, and the line at byte `n`.
pub open spec fn spec_bad_prefix(t: Seq<u8>, n: nat) -> (u32, Seq<u32>)
    decreases n,
{
    if n == 0 {
        (1, Seq::empty())
    } else {
        let (line, bad) = spec_bad_prefix(t, (n - 1) as nat);
        let i = n - 1;
        let bad2 = if !byte_ok(t, i) && (bad.len() == 0 || bad.last() != line) { bad.push(line) } else { bad };
        let line2 = if t[i] == 10 { (line + 1) as u32 } else { line };
        (line2, bad2)
    }
}

proof fn lemma_bad_prefix(t: Seq<u8>, n: nat)
    requires
        n <= t.len(),
    ensures
        spec_bad_prefix(t, n).0 <= n + 1,
        spec_bad_prefix(t, n).1.len() == 0 <==> forall|i: int| 0 <= i < n ==> byte_ok(t, i),
    decreases n,
{
    if n > 0 {
        lemma_bad_prefix(t, (n - 1) as nat);
    }
}

// ------------------------------------------------------------------ the lexer

/// A token of the companion file. A word holds its span, its line, and the word before it: 0 for none, 1 for `function` or
/// `predicate`, 2 for `lemma`. A comment makes no token.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Tok {
    Word(usize, usize, u32, u8),
    Quote(u32),
    At(u32),
    Attribute(u32),
}

/// Where the lexer stands. `Word` holds the start of the word. `Str` is a string, and `Esc` the byte after a backslash in one.
/// `SkipToBlock` and `SkipToCode` pass over the second byte of `/*`, `*/` or `{:`.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Mode {
    Code,
    Word(usize),
    Digits,
    LineComment,
    Str,
    Esc,
    Block,
    SkipToBlock,
    SkipToCode,
}

/// The state of the lexer. It is public because the open spec of `View` reads its fields.
pub struct Lx {
    pub line: u32,
    pub depth: usize,
    pub opened: u32,
    pub after: u8,
    pub mode: Mode,
    pub toks: Vec<Tok>,
}

pub ghost struct SLx {
    pub line: u32,
    pub depth: usize,
    pub opened: u32,
    pub after: u8,
    pub mode: Mode,
    pub toks: Seq<Tok>,
}

impl View for Lx {
    type V = SLx;

    open spec fn view(&self) -> SLx {
        SLx { line: self.line, depth: self.depth, opened: self.opened, after: self.after, mode: self.mode, toks: self.toks@ }
    }
}

pub open spec fn is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5a) || (0x61 <= c <= 0x7a)
}

pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// A byte that starts a word: a letter, `_` or `?`.
pub open spec fn word_start(c: u8) -> bool {
    is_alpha(c) || c == 0x5f || c == 0x3f
}

/// A byte inside a word: a letter, a digit, `_`, `'` or `?`.
pub open spec fn word_byte(c: u8) -> bool {
    is_alpha(c) || is_digit(c) || c == 0x5f || c == 0x27 || c == 0x3f
}

/// The byte after `i`, or 0 at the end.
pub open spec fn next(t: Seq<u8>, i: int) -> u8 {
    if i + 1 < t.len() { t[i + 1] } else { 0 }
}

pub open spec fn spec_is(t: Seq<u8>, s: int, e: int, w: Seq<u8>) -> bool {
    0 <= s <= e <= t.len() && t.subrange(s, e) == w
}

/// The word before a name: 1 for `function` and `predicate`, 2 for `lemma`, else 0.
pub open spec fn spec_decl(t: Seq<u8>, s: int, e: int) -> u8 {
    if spec_is(t, s, e, b"function"@) || spec_is(t, s, e, b"predicate"@) {
        1
    } else if spec_is(t, s, e, b"lemma"@) {
        2
    } else {
        0
    }
}

/// The lexer at a byte in code: `c` at `i` with the state `st`.
pub open spec fn spec_code(st: SLx, t: Seq<u8>, i: int) -> SLx {
    let c = t[i];
    if c == 10 {
        SLx { line: (st.line + 1) as u32, ..st }
    } else if c == 0x2f && next(t, i) == 0x2f {
        // A comment does not part a name from `function`, so `after` stays.
        SLx { mode: Mode::LineComment, ..st }
    } else if c == 0x2f && next(t, i) == 0x2a {
        SLx { opened: st.line, depth: 1, mode: Mode::SkipToBlock, ..st }
    } else if word_start(c) {
        SLx { mode: Mode::Word(i as usize), ..st }
    } else if is_digit(c) {
        SLx { after: 0, mode: Mode::Digits, ..st }
    } else if c == 0x22 {
        SLx { after: 0, mode: Mode::Str, toks: st.toks.push(Tok::Quote(st.line)), ..st }
    } else if c == 0x40 {
        SLx { after: 0, toks: st.toks.push(Tok::At(st.line)), ..st }
    } else if c == 0x7b && next(t, i) == 0x3a {
        SLx { after: 0, mode: Mode::SkipToCode, toks: st.toks.push(Tok::Attribute(st.line)), ..st }
    } else if c == 0x20 || c == 9 || c == 13 {
        st
    } else {
        SLx { after: 0, ..st }
    }
}

/// The word from `s` to `e` ends: its token, and the word it is for the name after it.
pub open spec fn spec_end_word(st: SLx, t: Seq<u8>, s: int, e: int) -> SLx {
    SLx {
        after: spec_decl(t, s, e),
        mode: Mode::Code,
        toks: st.toks.push(Tok::Word(s as usize, e as usize, st.line, st.after)),
        ..st
    }
}

/// One byte of the lexer.
pub open spec fn spec_step(st: SLx, t: Seq<u8>, i: int) -> SLx {
    let c = t[i];
    match st.mode {
        Mode::Code => spec_code(st, t, i),
        Mode::Word(s) => if word_byte(c) {
            st
        } else {
            spec_code(spec_end_word(st, t, s as int, i), t, i)
        },
        Mode::Digits => if is_digit(c) {
            st
        } else {
            spec_code(SLx { mode: Mode::Code, ..st }, t, i)
        },
        Mode::LineComment => if c == 10 {
            SLx { line: (st.line + 1) as u32, mode: Mode::Code, ..st }
        } else {
            st
        },
        // A string ends at its quote or at the end of its line.
        Mode::Str => if c == 0x22 {
            SLx { mode: Mode::Code, ..st }
        } else if c == 0x5c {
            SLx { mode: Mode::Esc, ..st }
        } else if c == 10 {
            SLx { line: (st.line + 1) as u32, mode: Mode::Code, ..st }
        } else {
            st
        },
        Mode::Esc => if c == 10 {
            SLx { line: (st.line + 1) as u32, mode: Mode::Code, ..st }
        } else {
            SLx { mode: Mode::Str, ..st }
        },
        // Comments nest, as in Dafny.
        Mode::Block => if c == 0x2f && next(t, i) == 0x2a {
            SLx { depth: (st.depth + 1) as usize, mode: Mode::SkipToBlock, ..st }
        } else if c == 0x2a && next(t, i) == 0x2f {
            SLx { depth: (st.depth - 1) as usize, mode: if st.depth == 1 { Mode::SkipToCode } else { Mode::SkipToBlock }, ..st }
        } else if c == 10 {
            SLx { line: (st.line + 1) as u32, ..st }
        } else {
            st
        },
        Mode::SkipToBlock => SLx { mode: Mode::Block, ..st },
        Mode::SkipToCode => SLx { mode: Mode::Code, ..st },
    }
}

pub open spec fn spec_start() -> SLx {
    SLx { line: 1, depth: 0, opened: 0, after: 0, mode: Mode::Code, toks: Seq::empty() }
}

/// The lexer after the first `n` bytes.
pub open spec fn spec_lex_prefix(t: Seq<u8>, n: nat) -> SLx
    decreases n,
{
    if n == 0 {
        spec_start()
    } else {
        spec_step(spec_lex_prefix(t, (n - 1) as nat), t, n - 1)
    }
}

/// The lexer at the end of the file: a word that runs to the end ends there.
pub open spec fn spec_lex(t: Seq<u8>) -> SLx {
    let st = spec_lex_prefix(t, t.len());
    match st.mode {
        Mode::Word(s) => spec_end_word(st, t, s as int, t.len() as int),
        _ => st,
    }
}

/// Each word token has a span inside the first `n` bytes.
pub open spec fn spans_ok(toks: Seq<Tok>, n: int) -> bool {
    forall|k: int| 0 <= k < toks.len() ==> match #[trigger] toks[k] {
        Tok::Word(s, e, _, _) => s <= e <= n,
        _ => true,
    }
}

/// What the lexer keeps true at byte `n`.
pub open spec fn lex_ok(st: SLx, n: int) -> bool {
    &&& st.line <= n + 1
    &&& st.depth <= n
    &&& (st.depth > 0 <==> (st.mode == Mode::Block || st.mode == Mode::SkipToBlock))
    &&& (st.mode matches Mode::Word(s) ==> s < n)
    &&& spans_ok(st.toks, n)
}

proof fn lemma_lex_prefix(t: Seq<u8>, n: nat)
    requires
        n <= t.len(),
        t.len() < u32::MAX,
    ensures
        lex_ok(spec_lex_prefix(t, n), n as int),
    decreases n,
{
    if n > 0 {
        lemma_lex_prefix(t, (n - 1) as nat);
        let st = spec_lex_prefix(t, (n - 1) as nat);
        let r = spec_lex_prefix(t, n);
        assert(r == spec_step(st, t, n - 1));
        assert(spans_ok(r.toks, n as int)) by {
            assert forall|k: int| 0 <= k < r.toks.len() implies match #[trigger] r.toks[k] {
                Tok::Word(s, e, _, _) => s <= e <= n,
                _ => true,
            } by {
                if k < st.toks.len() {
                    assert(r.toks[k] == st.toks[k]) by {
                        // Each step only pushes, so the old tokens stay.
                        lemma_step_keeps(st, t, n - 1);
                    }
                }
            }
        }
    }
}

/// Code pushes no token, or one that is no word, and keeps the other fields that the invariant reads.
proof fn lemma_code_keeps(st: SLx, t: Seq<u8>, i: int)
    requires
        0 <= i < t.len(),
    ensures
        ({
            let r = spec_code(st, t, i);
            &&& st.toks.len() <= r.toks.len() <= st.toks.len() + 1
            &&& forall|k: int| 0 <= k < st.toks.len() ==> #[trigger] r.toks[k] == st.toks[k]
            &&& r.toks.len() > st.toks.len() ==> !(r.toks[st.toks.len() as int] is Word)
        }),
{
    let c = t[i];
    let r = spec_code(st, t, i);
    if c == 0x22 {
        assert(r.toks == st.toks.push(Tok::Quote(st.line)));
    } else if c == 0x40 {
        assert(r.toks == st.toks.push(Tok::At(st.line)));
    } else if c == 0x7b && next(t, i) == 0x3a {
        assert(r.toks == st.toks.push(Tok::Attribute(st.line)));
    }
}

/// A step keeps the old tokens. A token that it pushes is a word with a span that ends at `i`, or no word.
proof fn lemma_step_keeps(st: SLx, t: Seq<u8>, i: int)
    requires
        0 <= i < t.len(),
        t.len() < u32::MAX,
        lex_ok(st, i),
    ensures
        ({
            let r = spec_step(st, t, i);
            &&& st.toks.len() <= r.toks.len()
            &&& forall|k: int| 0 <= k < st.toks.len() ==> #[trigger] r.toks[k] == st.toks[k]
            &&& forall|k: int| st.toks.len() <= k < r.toks.len() ==> match #[trigger] r.toks[k] {
                Tok::Word(s, e, _, _) => s <= e <= i,
                _ => true,
            }
        }),
{
    let c = t[i];
    let r = spec_step(st, t, i);
    match st.mode {
        Mode::Code => {
            lemma_code_keeps(st, t, i);
        },
        Mode::Word(s) => {
            if !word_byte(c) {
                let w = spec_end_word(st, t, s as int, i);
                assert(w.toks == st.toks.push(Tok::Word(s, i as usize, st.line, st.after)));
                lemma_code_keeps(w, t, i);
                assert(r == spec_code(w, t, i));
                assert(r.toks[st.toks.len() as int] == Tok::Word(s, i as usize, st.line, st.after));
            }
        },
        Mode::Digits => {
            if !is_digit(c) {
                lemma_code_keeps(SLx { mode: Mode::Code, ..st }, t, i);
            }
        },
        _ => {},
    }
}

// ------------------------------------------------------------------ the rule

/// A keyword of Dafny that is not on the short list of decision 0080.
pub open spec fn spec_banned(t: Seq<u8>, s: int, e: int) -> bool {
    let w = t.subrange(s, e);
    w == b"abstract"@ || w == b"allocated"@ || w == b"array"@ || w == b"assume"@ || w == b"break"@ || w == b"by"@ || w == b"calc"@ || w == b"char"@
        || w == b"class"@ || w == b"codatatype"@ || w == b"colemma"@ || w == b"comethod"@ || w == b"const"@ || w == b"constructor"@
        || w == b"continue"@ || w == b"copredicate"@ || w == b"datatype"@ || w == b"default"@ || w == b"expect"@ || w == b"export"@
        || w == b"extends"@ || w == b"for"@ || w == b"fresh"@ || w == b"greatest"@ || w == b"imap"@ || w == b"import"@ || w == b"include"@
        || w == b"inductive"@ || w == b"invariant"@ || w == b"iset"@ || w == b"iterator"@ || w == b"label"@ || w == b"least"@
        || w == b"method"@ || w == b"modifies"@ || w == b"modify"@ || w == b"module"@ || w == b"nameonly"@ || w == b"new"@
        || w == b"newtype"@ || w == b"null"@ || w == b"object"@ || w == b"old"@ || w == b"opaque"@ || w == b"opened"@
        || w == b"ORDINAL"@ || w == b"print"@ || w == b"provides"@ || w == b"real"@ || w == b"refines"@ || w == b"return"@
        || w == b"returns"@ || w == b"reveal"@ || w == b"reveals"@ || w == b"static"@ || w == b"string"@ || w == b"this"@
        || w == b"to"@ || w == b"trait"@ || w == b"twostate"@ || w == b"type"@ || w == b"unchanged"@ || w == b"while"@
        || w == b"witness"@ || w == b"yield"@ || w == b"yields"@
}

/// `w` starts the bytes from `s` to `e`.
pub open spec fn spec_starts(t: Seq<u8>, s: int, e: int, w: Seq<u8>) -> bool {
    w.len() <= e - s && t.subrange(s, s + w.len()) == w
}

/// A name of the prelude, or a name with a prefix of the model, decision 0083.
pub open spec fn spec_model_name(t: Seq<u8>, s: int, e: int) -> bool {
    let w = t.subrange(s, e);
    w == b"Option"@ || w == b"Some"@ || w == b"None"@ || w == b"Vec"@ || w == b"value"@ || w == b"int8"@ || w == b"int16"@
        || w == b"uint16"@ || w == b"int32"@ || w == b"int64"@ || w == b"uint8"@ || w == b"uint32"@ || w == b"uint64"@ || w == b"shr"@
        || w == b"CountIf"@ || w == b"Double"@ || w == b"abs"@ || w == b"round"@ || w == b"fadd"@ || w == b"fsub"@ || w == b"fmul"@
        || w == b"fdiv"@ || w == b"fint"@ || w == b"EPS"@ || w == b"ETA"@ || w == b"MAX"@ || w == b"RoundError"@ || w == b"RoundExactInt"@
        || w == b"Algorithm"@ || w == b"StdSort"@ || w == b"StrictWeakOrder"@ || w == b"SortedBy"@
        || spec_starts(t, s, e, b"v_"@) || spec_starts(t, s, e, b"c_"@) || spec_starts(t, s, e, b"S_"@) || spec_starts(t, s, e, b"E_"@)
        || spec_starts(t, s, e, b"f_"@) || spec_starts(t, s, e, b"b_"@) || spec_starts(t, s, e, b"trunc_"@)
}

/// The refusals of one token.
pub open spec fn spec_tok_refusals(t: Seq<u8>, k: Tok) -> Seq<(u32, CompanionRefusal)> {
    match k {
        Tok::Word(s, e, l, a) => {
            let name = if a != 0 && spec_model_name(t, s as int, e as int) {
                seq![(l, CompanionRefusal::ModelName(s, e))]
            } else {
                Seq::empty()
            };
            if spec_banned(t, s as int, e as int) {
                name.push((l, CompanionRefusal::Word(s, e)))
            } else {
                name
            }
        },
        Tok::Quote(l) => seq![(l, CompanionRefusal::Quote)],
        Tok::At(l) => seq![(l, CompanionRefusal::At)],
        Tok::Attribute(l) => seq![(l, CompanionRefusal::Attribute)],
    }
}

/// The refusals of the first `n` tokens, in order.
pub open spec fn spec_refusals(t: Seq<u8>, toks: Seq<Tok>, n: nat) -> Seq<(u32, CompanionRefusal)>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        spec_refusals(t, toks, (n - 1) as nat) + spec_tok_refusals(t, toks[n - 1])
    }
}

/// The names that the first `n` tokens declare, in order.
pub open spec fn spec_declared(toks: Seq<Tok>, n: nat) -> Seq<(usize, usize, u32, bool)>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        let d = spec_declared(toks, (n - 1) as nat);
        match toks[n - 1] {
            Tok::Word(s, e, l, a) => if a != 0 { d.push((s, e, l, a == 2)) } else { d },
            _ => d,
        }
    }
}

/// A token that the rules allow.
pub open spec fn tok_ok(t: Seq<u8>, k: Tok) -> bool {
    match k {
        Tok::Word(s, e, _, a) => !spec_banned(t, s as int, e as int) && (a != 0 ==> !spec_model_name(t, s as int, e as int)),
        _ => false,
    }
}

proof fn lemma_refusals_empty(t: Seq<u8>, toks: Seq<Tok>, n: nat)
    requires
        n <= toks.len(),
    ensures
        spec_refusals(t, toks, n).len() == 0 <==> forall|k: int| 0 <= k < n ==> tok_ok(t, #[trigger] toks[k]),
    decreases n,
{
    if n > 0 {
        lemma_refusals_empty(t, toks, (n - 1) as nat);
        let last = toks[n - 1];
        assert(spec_tok_refusals(t, last).len() == 0 <==> tok_ok(t, last));
    }
}

/// The result of the scan, decisions 0080 and 0083. A refused byte stops the scan. Else each token is read, and a comment that
/// does not end is refused at its first line.
pub open spec fn spec_scan(t: Seq<u8>) -> (Seq<(u32, CompanionRefusal)>, Seq<(usize, usize, u32, bool)>) {
    let bad = spec_bad_prefix(t, t.len()).1;
    if bad.len() > 0 {
        (bad.map_values(|l: u32| (l, CompanionRefusal::Char)), Seq::empty())
    } else {
        let st = spec_lex(t);
        let r = spec_refusals(t, st.toks, st.toks.len());
        let r2 = if st.depth > 0 { r.push((st.opened, CompanionRefusal::Unclosed)) } else { r };
        if r2.len() > 0 {
            (r2, Seq::empty())
        } else {
            (r2, spec_declared(st.toks, st.toks.len()))
        }
    }
}

/// A file that passes: each byte allowed, each comment closed, each token allowed, decision 0123.
pub open spec fn spec_passes(t: Seq<u8>) -> bool {
    let st = spec_lex(t);
    &&& forall|i: int| 0 <= i < t.len() ==> byte_ok(t, i)
    &&& st.depth == 0
    &&& forall|k: int| 0 <= k < st.toks.len() ==> tok_ok(t, #[trigger] st.toks[k])
}

proof fn lemma_scan_passes(t: Seq<u8>)
    requires
        t.len() < u32::MAX,
    ensures
        spec_scan(t).0.len() == 0 <==> spec_passes(t),
{
    lemma_bad_prefix(t, t.len());
    let bad = spec_bad_prefix(t, t.len()).1;
    if bad.len() == 0 {
        let st = spec_lex(t);
        lemma_refusals_empty(t, st.toks, st.toks.len());
        lemma_lex_prefix(t, t.len());
    } else {
        assert(bad.map_values(|l: u32| (l, CompanionRefusal::Char)).len() == bad.len());
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

fn starts(t: &Vec<u8>, s: usize, e: usize, w: &[u8]) -> (r: bool)
    requires
        s <= e <= t.len(),
    ensures
        r == spec_starts(t@, s as int, e as int, w@),
{
    if w.len() > e - s {
        return false;
    }
    word_is(t, s, s + w.len(), w)
}

fn decl(t: &Vec<u8>, s: usize, e: usize) -> (r: u8)
    requires
        s <= e <= t.len(),
    ensures
        r == spec_decl(t@, s as int, e as int),
{
    if word_is(t, s, e, b"function") || word_is(t, s, e, b"predicate") {
        1
    } else if word_is(t, s, e, b"lemma") {
        2
    } else {
        0
    }
}

fn banned(t: &Vec<u8>, s: usize, e: usize) -> (r: bool)
    requires
        s <= e <= t.len(),
    ensures
        r == spec_banned(t@, s as int, e as int),
{
    let w = |x: &[u8]| -> (r: bool)
        requires
            s <= e <= t.len(),
        ensures
            r == (t@.subrange(s as int, e as int) == x@),
        { word_is(t, s, e, x) };
    w(b"abstract") || w(b"allocated") || w(b"array") || w(b"assume") || w(b"break") || w(b"by") || w(b"calc") || w(b"char") || w(b"class")
        || w(b"codatatype") || w(b"colemma") || w(b"comethod") || w(b"const") || w(b"constructor") || w(b"continue")
        || w(b"copredicate") || w(b"datatype") || w(b"default") || w(b"expect") || w(b"export") || w(b"extends") || w(b"for") || w(b"fresh")
        || w(b"greatest") || w(b"imap") || w(b"import") || w(b"include") || w(b"inductive") || w(b"invariant") || w(b"iset")
        || w(b"iterator") || w(b"label") || w(b"least") || w(b"method") || w(b"modifies") || w(b"modify") || w(b"module")
        || w(b"nameonly") || w(b"new") || w(b"newtype") || w(b"null") || w(b"object") || w(b"old") || w(b"opaque") || w(b"opened")
        || w(b"ORDINAL") || w(b"print") || w(b"provides") || w(b"real") || w(b"refines") || w(b"return") || w(b"returns")
        || w(b"reveal") || w(b"reveals") || w(b"static") || w(b"string") || w(b"this") || w(b"to") || w(b"trait") || w(b"twostate")
        || w(b"type") || w(b"unchanged") || w(b"while") || w(b"witness") || w(b"yield") || w(b"yields")
}

fn model_name(t: &Vec<u8>, s: usize, e: usize) -> (r: bool)
    requires
        s <= e <= t.len(),
    ensures
        r == spec_model_name(t@, s as int, e as int),
{
    let w = |x: &[u8]| -> (r: bool)
        requires
            s <= e <= t.len(),
        ensures
            r == (t@.subrange(s as int, e as int) == x@),
        { word_is(t, s, e, x) };
    let p = |x: &[u8]| -> (r: bool)
        requires
            s <= e <= t.len(),
        ensures
            r == spec_starts(t@, s as int, e as int, x@),
        { starts(t, s, e, x) };
    w(b"Option") || w(b"Some") || w(b"None") || w(b"Vec") || w(b"value") || w(b"int8") || w(b"int16") || w(b"uint16") || w(b"int32")
        || w(b"int64") || w(b"uint8") || w(b"uint32") || w(b"uint64") || w(b"shr") || w(b"CountIf") || w(b"Double") || w(b"abs") || w(b"round") || w(b"fadd")
        || w(b"fsub") || w(b"fmul") || w(b"fdiv") || w(b"fint") || w(b"EPS") || w(b"ETA") || w(b"MAX") || w(b"RoundError") || w(b"RoundExactInt") || w(b"Algorithm") || w(b"StdSort")
        || w(b"StrictWeakOrder") || w(b"SortedBy") || p(b"v_") || p(b"c_") || p(b"S_") || p(b"E_")
        || p(b"f_") || p(b"b_") || p(b"trunc_")
}

fn next_byte(t: &Vec<u8>, i: usize) -> (r: u8)
    requires
        i < t.len(),
    ensures
        r == next(t@, i as int),
{
    if i + 1 < t.len() {
        t[i + 1]
    } else {
        0
    }
}

fn code(st: &mut Lx, t: &Vec<u8>, i: usize)
    requires
        i < t.len(),
        old(st).line <= i + 1,
        t.len() < u32::MAX,
    ensures
        final(st)@ == spec_code(old(st)@, t@, i as int),
{
    let c = t[i];
    if c == 10 {
        st.line = st.line + 1;
    } else if c == 0x2f && next_byte(t, i) == 0x2f {
        st.mode = Mode::LineComment;
    } else if c == 0x2f && next_byte(t, i) == 0x2a {
        st.opened = st.line;
        st.depth = 1;
        st.mode = Mode::SkipToBlock;
    } else if (0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || c == 0x5f || c == 0x3f {
        st.mode = Mode::Word(i);
    } else if 0x30 <= c && c <= 0x39 {
        st.after = 0;
        st.mode = Mode::Digits;
    } else if c == 0x22 {
        st.after = 0;
        st.mode = Mode::Str;
        st.toks.push(Tok::Quote(st.line));
    } else if c == 0x40 {
        st.after = 0;
        st.toks.push(Tok::At(st.line));
    } else if c == 0x7b && next_byte(t, i) == 0x3a {
        st.after = 0;
        st.mode = Mode::SkipToCode;
        st.toks.push(Tok::Attribute(st.line));
    } else if c == 0x20 || c == 9 || c == 13 {
    } else {
        st.after = 0;
    }
}

fn step(st: &mut Lx, t: &Vec<u8>, i: usize)
    requires
        i < t.len(),
        t.len() < u32::MAX,
        lex_ok(old(st)@, i as int),
    ensures
        final(st)@ == spec_step(old(st)@, t@, i as int),
{
    let c = t[i];
    match st.mode {
        Mode::Code => code(st, t, i),
        Mode::Word(s) => {
            if !((0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || (0x30 <= c && c <= 0x39) || c == 0x5f || c == 0x27 || c == 0x3f) {
                let a = decl(t, s, i);
                st.toks.push(Tok::Word(s, i, st.line, st.after));
                st.after = a;
                st.mode = Mode::Code;
                code(st, t, i);
            }
        },
        Mode::Digits => {
            if !(0x30 <= c && c <= 0x39) {
                st.mode = Mode::Code;
                code(st, t, i);
            }
        },
        Mode::LineComment => {
            if c == 10 {
                st.line = st.line + 1;
                st.mode = Mode::Code;
            }
        },
        Mode::Str => {
            if c == 0x22 {
                st.mode = Mode::Code;
            } else if c == 0x5c {
                st.mode = Mode::Esc;
            } else if c == 10 {
                st.line = st.line + 1;
                st.mode = Mode::Code;
            }
        },
        Mode::Esc => {
            if c == 10 {
                st.line = st.line + 1;
                st.mode = Mode::Code;
            } else {
                st.mode = Mode::Str;
            }
        },
        Mode::Block => {
            if c == 0x2f && next_byte(t, i) == 0x2a {
                st.depth = st.depth + 1;
                st.mode = Mode::SkipToBlock;
            } else if c == 0x2a && next_byte(t, i) == 0x2f {
                st.mode = if st.depth == 1 { Mode::SkipToCode } else { Mode::SkipToBlock };
                st.depth = st.depth - 1;
            } else if c == 10 {
                st.line = st.line + 1;
            }
        },
        Mode::SkipToBlock => st.mode = Mode::Block,
        Mode::SkipToCode => st.mode = Mode::Code,
    }
}

fn lex(t: &Vec<u8>) -> (r: Lx)
    requires
        t.len() < u32::MAX,
    ensures
        r@ == spec_lex(t@),
        lex_ok(r@, t.len() as int),
{
    let mut st = Lx { line: 1, depth: 0, opened: 0, after: 0, mode: Mode::Code, toks: Vec::new() };
    let mut i = 0;
    proof {
        assert(st@ =~= spec_start());
    }
    while i < t.len()
        invariant
            i <= t.len(),
            t.len() < u32::MAX,
            st@ == spec_lex_prefix(t@, i as nat),
            lex_ok(st@, i as int),
        decreases t.len() - i,
    {
        proof {
            lemma_lex_prefix(t@, (i + 1) as nat);
        }
        step(&mut st, t, i);
        i += 1;
    }
    if let Mode::Word(s) = st.mode {
        let a = decl(t, s, t.len());
        st.toks.push(Tok::Word(s, t.len(), st.line, st.after));
        st.after = a;
        st.mode = Mode::Code;
        proof {
            assert(spans_ok(st@.toks, t.len() as int)) by {
                assert forall|k: int| 0 <= k < st@.toks.len() implies match #[trigger] st@.toks[k] {
                    Tok::Word(s, e, _, _) => s <= e <= t.len(),
                    _ => true,
                } by {}
            }
        }
    }
    st
}

/// The line of each refused byte, once for each line, decision 0083.
fn bad_lines(t: &Vec<u8>) -> (r: Vec<u32>)
    requires
        t.len() < u32::MAX,
    ensures
        r@ == spec_bad_prefix(t@, t.len() as nat).1,
{
    let mut bad: Vec<u32> = Vec::new();
    let mut line: u32 = 1;
    let mut i = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            t.len() < u32::MAX,
            (line, bad@) == spec_bad_prefix(t@, i as nat),
        decreases t.len() - i,
    {
        proof {
            lemma_bad_prefix(t@, i as nat);
        }
        let c = t[i];
        let ok = (0x20 <= c && c <= 0x7e) || c == 9 || c == 10 || (c == 13 && i + 1 < t.len() && t[i + 1] == 10);
        if !ok && (bad.len() == 0 || bad[bad.len() - 1] != line) {
            bad.push(line);
        }
        if c == 10 {
            line = line + 1;
        }
        i += 1;
    }
    bad
}

/// The scan of the companion file, decision 0123. A file passes only when each byte is allowed, each comment ends, and each
/// token is allowed.
pub fn scan_companion(t: &Vec<u8>) -> (r: CompanionScan)
    requires
        t.len() < u32::MAX,
    ensures
        (r.refusals@, r.declared@) == spec_scan(t@),
        r.refusals@.len() == 0 <==> spec_passes(t@),
{
    proof {
        lemma_scan_passes(t@);
    }
    let bad = bad_lines(t);
    if bad.len() > 0 {
        let mut refusals: Vec<(u32, CompanionRefusal)> = Vec::new();
        let mut i = 0;
        while i < bad.len()
            invariant
                i <= bad.len(),
                refusals@ == bad@.subrange(0, i as int).map_values(|l: u32| (l, CompanionRefusal::Char)),
            decreases bad.len() - i,
        {
            refusals.push((bad[i], CompanionRefusal::Char));
            i += 1;
            proof {
                assert(bad@.subrange(0, i as int).map_values(|l: u32| (l, CompanionRefusal::Char)) =~= refusals@);
            }
        }
        proof {
            assert(bad@.subrange(0, bad.len() as int) =~= bad@);
        }
        return CompanionScan { refusals, declared: Vec::new() };
    }
    let st = lex(t);
    let mut refusals: Vec<(u32, CompanionRefusal)> = Vec::new();
    let mut declared: Vec<(usize, usize, u32, bool)> = Vec::new();
    let mut k = 0;
    while k < st.toks.len()
        invariant
            k <= st.toks.len(),
            st@ == spec_lex(t@),
            lex_ok(st@, t.len() as int),
            refusals@ == spec_refusals(t@, st@.toks, k as nat),
            declared@ == spec_declared(st@.toks, k as nat),
        decreases st.toks.len() - k,
    {
        let tok = st.toks[k];
        assert(spans_ok(st@.toks, t.len() as int));
        assert(st@.toks[k as int] == tok);
        match tok {
            Tok::Word(s, e, l, a) => {
                if a != 0 && model_name(t, s, e) {
                    refusals.push((l, CompanionRefusal::ModelName(s, e)));
                }
                if banned(t, s, e) {
                    refusals.push((l, CompanionRefusal::Word(s, e)));
                }
                if a != 0 {
                    declared.push((s, e, l, a == 2));
                }
            },
            Tok::Quote(l) => refusals.push((l, CompanionRefusal::Quote)),
            Tok::At(l) => refusals.push((l, CompanionRefusal::At)),
            Tok::Attribute(l) => refusals.push((l, CompanionRefusal::Attribute)),
        }
        k += 1;
        proof {
            assert(refusals@ =~= spec_refusals(t@, st@.toks, k as nat));
        }
    }
    if st.depth > 0 {
        refusals.push((st.opened, CompanionRefusal::Unclosed));
    }
    if refusals.len() > 0 {
        declared = Vec::new();
    }
    CompanionScan { refusals, declared }
}

} // verus!

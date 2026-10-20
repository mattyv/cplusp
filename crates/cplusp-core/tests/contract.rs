//! The lexer of a contract line in the core, decisions 0082, 0106 and 0124. Each test gives the bytes of a line and reads the
//! tokens with the text of their spans.

use cplusp_core::contract::*;
use cplusp_core::model::{BinOp, Tok};

/// The tokens as (text of the span, kind).
fn lex(text: &str) -> Vec<(String, LexKind)> {
    let bytes = text.as_bytes().to_vec();
    lex_contract(&bytes).into_iter().map(|l| (String::from_utf8(bytes[l.start..l.end].to_vec()).unwrap(), l.kind)).collect()
}

fn t(s: &str, k: LexKind) -> (String, LexKind) {
    (s.to_string(), k)
}

fn name(s: &str) -> (String, LexKind) {
    t(s, LexKind::Name(false))
}

fn fixed(s: &str, k: Tok) -> (String, LexKind) {
    t(s, LexKind::Fixed(k))
}

fn op(s: &str, o: BinOp) -> (String, LexKind) {
    fixed(s, Tok::Op(o))
}

#[test]
fn names_numbers_and_operators() {
    assert_eq!(lex("x + 1 <= y"), vec![name("x"), op("+", BinOp::Add), t("1", LexKind::Int(1)), op("<=", BinOp::Le), name("y")]);
}

#[test]
fn each_operator_takes_its_longest_form() {
    assert_eq!(
        lex("a ==> b || c != d >= e - f * g / h % i == j < k > l && m"),
        vec![
            name("a"),
            op("==>", BinOp::Implies),
            name("b"),
            op("||", BinOp::Or),
            name("c"),
            op("!=", BinOp::Ne),
            name("d"),
            op(">=", BinOp::Ge),
            name("e"),
            op("-", BinOp::Sub),
            name("f"),
            op("*", BinOp::Mul),
            name("g"),
            op("/", BinOp::Div),
            name("h"),
            op("%", BinOp::Rem),
            name("i"),
            op("==", BinOp::Eq),
            name("j"),
            op("<", BinOp::Lt),
            name("k"),
            op(">", BinOp::Gt),
            name("l"),
            op("&&", BinOp::And),
            name("m"),
        ]
    );
}

#[test]
fn the_words_of_the_grammar_and_old_only_before_a_parenthesis() {
    assert_eq!(
        lex("old(x) == result && old + 1 > 0 && old (y) && forall exists true false"),
        vec![
            fixed("old", Tok::Old),
            fixed("(", Tok::LParen),
            name("x"),
            fixed(")", Tok::RParen),
            op("==", BinOp::Eq),
            fixed("result", Tok::Result),
            op("&&", BinOp::And),
            name("old"),
            op("+", BinOp::Add),
            t("1", LexKind::Int(1)),
            op(">", BinOp::Gt),
            t("0", LexKind::Int(0)),
            op("&&", BinOp::And),
            fixed("old", Tok::Old),
            fixed("(", Tok::LParen),
            name("y"),
            fixed(")", Tok::RParen),
            op("&&", BinOp::And),
            fixed("forall", Tok::Forall),
            fixed("exists", Tok::Exists),
            fixed("true", Tok::Bool(true)),
            fixed("false", Tok::Bool(false)),
        ]
    );
}

#[test]
fn a_name_before_a_parenthesis_is_a_call() {
    let toks = lex("f(x) && g (y) && h");
    assert_eq!(toks[0], t("f", LexKind::Name(true)));
    assert_eq!(toks[5], t("g", LexKind::Name(true)));
    assert_eq!(toks[10], t("h", LexKind::Name(false)));
}

#[test]
fn a_number_is_decimal_or_hex_with_separators_and_a_suffix() {
    assert_eq!(
        lex("0x1F 1'000 42ull 0 7LU 0X0 18446744073709551615"),
        vec![
            t("0x1F", LexKind::Int(31)),
            t("1'000", LexKind::Int(1000)),
            t("42ull", LexKind::Int(42)),
            t("0", LexKind::Int(0)),
            t("7LU", LexKind::Int(7)),
            t("0X0", LexKind::Int(0)),
            t("18446744073709551615", LexKind::Int(u64::MAX)),
        ]
    );
}

#[test]
fn a_number_that_cannot_be_read_is_never_a_value() {
    assert_eq!(
        lex("0x 017 12q 18446744073709551616 1e5 0xg"),
        vec![
            t("0x", LexKind::BadNumber(NumberFault::NoDigits)),
            t("017", LexKind::BadNumber(NumberFault::Octal)),
            t("12q", LexKind::BadNumber(NumberFault::Suffix(1))),
            t("18446744073709551616", LexKind::BadNumber(NumberFault::TooBig)),
            t("1e5", LexKind::BadNumber(NumberFault::Suffix(2))),
            t("0xg", LexKind::BadNumber(NumberFault::NoDigits)),
        ]
    );
}

/// A bad suffix carries its length in the number without separators, so the shell names it as the author wrote it, decision 0124.
#[test]
fn a_bad_suffix_has_its_length_without_separators() {
    assert_eq!(lex("12u'q 0x1Fzz"), vec![t("12u'q", LexKind::BadNumber(NumberFault::Suffix(2))), t("0x1Fzz", LexKind::BadNumber(NumberFault::Suffix(2)))]);
}

#[test]
fn a_separator_only_stands_between_two_digits_or_letters() {
    // `1'` ends the number before the quote, and the quote is a character that a contract cannot hold.
    assert_eq!(lex("1' x"), vec![t("1", LexKind::Int(1)), t("'", LexKind::BadChar), name("x")]);
}

#[test]
fn the_methods_fields_slices_and_paths() {
    assert_eq!(
        lex("v.size() s.empty() o.has_value() o.value() p.x a[1..2] A::B v.size ()"),
        vec![
            name("v"),
            fixed(".size()", Tok::Size),
            name("s"),
            fixed(".empty()", Tok::Empty),
            name("o"),
            fixed(".has_value()", Tok::HasValue),
            name("o"),
            fixed(".value()", Tok::Value),
            name("p"),
            t(".x", LexKind::Field),
            name("a"),
            fixed("[", Tok::LBracket),
            t("1", LexKind::Int(1)),
            fixed("..", Tok::DotDot),
            t("2", LexKind::Int(2)),
            fixed("]", Tok::RBracket),
            name("A"),
            fixed("::", Tok::ColonColon),
            name("B"),
            name("v"),
            t(".size", LexKind::Field),
            fixed("(", Tok::LParen),
            fixed(")", Tok::RParen),
        ]
    );
}

#[test]
fn a_character_is_its_code_and_a_quote_alone_is_refused() {
    assert_eq!(lex("'a' == ' '"), vec![t("'a'", LexKind::Int(97)), op("==", BinOp::Eq), t("' '", LexKind::Int(32))]);
    assert_eq!(lex("'''"), vec![t("'", LexKind::BadChar), t("'", LexKind::BadChar), t("'", LexKind::BadChar)]);
    assert_eq!(lex("'\\n'"), vec![t("'", LexKind::BadChar), t("\\", LexKind::BadChar), name("n"), t("'", LexKind::BadChar)]);
}

#[test]
fn the_punctuation() {
    assert_eq!(
        lex("!(a) ? b : c, d"),
        vec![
            fixed("!", Tok::Bang),
            fixed("(", Tok::LParen),
            name("a"),
            fixed(")", Tok::RParen),
            fixed("?", Tok::Question),
            name("b"),
            fixed(":", Tok::Colon),
            name("c"),
            fixed(",", Tok::Comma),
            name("d"),
        ]
    );
}

#[test]
fn white_space_is_ascii_only_and_any_other_character_is_refused_whole() {
    assert_eq!(lex("\tx\r\n y\u{b}\u{c}z"), vec![name("x"), name("y"), name("z")]);
    // A no-break space is no white space in a contract, decision 0124.
    assert_eq!(lex("x\u{a0}y \u{e9} $"), vec![name("x"), t("\u{a0}", LexKind::BadChar), name("y"), t("\u{e9}", LexKind::BadChar), t("$", LexKind::BadChar)]);
}

/// The lexer drops no text except white space: the spans are in order, and each byte outside them is ASCII white space.
#[test]
fn the_spans_cover_every_byte_but_white_space() {
    for text in [
        "x + 1 <= y",
        "  old(a.size()) == result ==> forall i :: 0 <= i < 10 && v[i] != 'q'  ",
        "0x1F'FF 1'2'3ull 017 é ü \u{a0} $ @ # ~ ` ;",
        "a..b A::B c.d .e f(g, h) ? i : j",
        "",
        "   \t\r\n",
    ] {
        let bytes = text.as_bytes().to_vec();
        let toks = lex_contract(&bytes);
        let mut at = 0;
        for l in &toks {
            assert!(at <= l.start && l.start < l.end && l.end <= bytes.len(), "{text:?}");
            assert!(bytes[at..l.start].iter().all(|b| matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)), "{text:?}");
            at = l.end;
        }
        assert!(bytes[at..].iter().all(|b| matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)), "{text:?}");
    }
}

/// `->` is one token, before `-` and `>`, decision 0137.
#[test]
fn the_arrow_is_one_token() {
    assert_eq!(lex("result->lo"), vec![fixed("result", Tok::Result), fixed("->", Tok::Arrow), name("lo")]);
    assert_eq!(lex("a -> b - > c"), vec![name("a"), fixed("->", Tok::Arrow), name("b"), op("-", BinOp::Sub), op(">", BinOp::Gt), name("c")]);
    assert_eq!(lex("x-->0"), vec![name("x"), op("-", BinOp::Sub), fixed("->", Tok::Arrow), t("0", LexKind::Int(0))]);
    assert_eq!(lex("a ==> b"), vec![name("a"), op("==>", BinOp::Implies), name("b")]);
}

/// `nullptr` is a word of the grammar in a contract, decision 0140.
#[test]
fn nullptr_is_a_word() {
    assert_eq!(lex("p != nullptr"), vec![name("p"), op("!=", BinOp::Ne), fixed("nullptr", Tok::Nullptr)]);
    assert_eq!(lex("nullptr_t nullptrx"), vec![name("nullptr_t"), name("nullptrx")]);
}

/// A decimal literal with a point is a real, by its digits and the count of digits after the point, and `std::isfinite` is a word,
/// decision 0150.
#[test]
fn a_decimal_with_a_point_is_a_real_and_isfinite_is_a_word() {
    assert_eq!(lex("150.0 0.5 100.25"), vec![t("150.0", LexKind::Real(1500, 1)), t("0.5", LexKind::Real(5, 1)), t("100.25", LexKind::Real(10025, 2))]);
    assert_eq!(
        lex("std::isfinite(a)"),
        vec![fixed("std::isfinite", Tok::IsFinite), fixed("(", Tok::LParen), name("a"), fixed(")", Tok::RParen)]
    );
    // A point with no digit after it, and an exponent, have no rule.
    assert!(lex("1.").iter().any(|(_, k)| *k == LexKind::BadChar || matches!(k, LexKind::BadNumber(_))), "{:?}", lex("1."));
    assert!(lex("1.5e3").iter().any(|(_, k)| matches!(k, LexKind::BadNumber(_))), "{:?}", lex("1.5e3"));
    assert_eq!(lex("std::isfinitex"), vec![name("std"), fixed("::", Tok::ColonColon), name("isfinitex")]);
}

/// `|` is the bar of an absolute value, and `eps`, `eta` and `DBL_MAX` are words, decision 0154. `||` stays one operator.
#[test]
fn the_bar_and_the_words_of_a_double_bound() {
    assert_eq!(
        lex("|a| <= eps * DBL_MAX + eta || b"),
        vec![
            fixed("|", Tok::Bar),
            name("a"),
            fixed("|", Tok::Bar),
            op("<=", BinOp::Le),
            fixed("eps", Tok::Eps),
            op("*", BinOp::Mul),
            fixed("DBL_MAX", Tok::DblMax),
            op("+", BinOp::Add),
            fixed("eta", Tok::Eta),
            op("||", BinOp::Or),
            name("b"),
        ]
    );
    assert_eq!(lex("epsilon DBL_MAXX"), vec![name("epsilon"), name("DBL_MAXX")]);
}

/// A decimal with more than 19 digits after the point has its own fault, decision 0155.
#[test]
fn a_decimal_with_too_many_digits_after_the_point_has_its_own_fault() {
    assert_eq!(lex("0.00000000000000000001"), vec![t("0.00000000000000000001", LexKind::BadNumber(NumberFault::Scale))]);
    assert_eq!(lex("0.0000000000000000001"), vec![t("0.0000000000000000001", LexKind::Real(1, 19))]);
}


/// `this` is a word of the grammar, decision 0166. A name that starts with it is a name.
#[test]
fn this_is_a_word() {
    assert_eq!(lex("this->k_ == thisx"), vec![fixed("this", Tok::This), fixed("->", Tok::Arrow), name("k_"), op("==", BinOp::Eq), name("thisx")]);
}

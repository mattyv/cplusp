//! The scan of the companion file in the core, decisions 0080, 0083 and 0123. Each test gives the bytes of a file and reads the
//! refusals in the order of the scan, and the names that the file declares.

use cplusp_core::companion::*;

/// The refusals as (line, kind), with the word of a kind that has one, and the declarations as (name, line, lemma).
fn scan(text: &str) -> (Vec<(u32, String)>, Vec<(String, u32, bool)>) {
    let bytes = text.as_bytes().to_vec();
    let s = scan_companion(&bytes);
    let word = |a: usize, b: usize| String::from_utf8(bytes[a..b].to_vec()).unwrap();
    let refusals = s
        .refusals
        .iter()
        .map(|(line, k)| {
            let kind = match k {
                CompanionRefusal::Char => "char".to_string(),
                CompanionRefusal::Word(a, b) => format!("word:{}", word(*a, *b)),
                CompanionRefusal::Quote => "\"".to_string(),
                CompanionRefusal::At => "@".to_string(),
                CompanionRefusal::Attribute => "{:".to_string(),
                CompanionRefusal::ModelName(a, b) => format!("name:{}", word(*a, *b)),
                CompanionRefusal::Unclosed => "unclosed".to_string(),
            };
            (*line, kind)
        })
        .collect();
    let declared = s.declared.iter().map(|(a, b, line, lemma)| (word(*a, *b), *line, *lemma)).collect();
    (refusals, declared)
}

fn refused(v: &[(u32, &str)]) -> Vec<(u32, String)> {
    v.iter().map(|(l, k)| (*l, k.to_string())).collect()
}

#[test]
fn a_clean_file_declares_its_functions_predicates_and_lemmas() {
    let (r, d) = scan("function F(x: int): int { x }\npredicate P(x: int) { true }\nlemma L()\n  ensures true\n{}\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![("F".to_string(), 1, false), ("P".to_string(), 2, false), ("L".to_string(), 3, true)]);
}

#[test]
fn a_word_in_a_comment_is_no_word_and_comments_nest() {
    let (r, d) = scan("// assume\n/* method /* nested */ newtype */\nfunction F(): int { 1 }\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![("F".to_string(), 3, false)]);
}

#[test]
fn each_keyword_off_the_list_is_refused_and_the_file_declares_nothing() {
    let (r, d) = scan("method M() {}\nfunction F(): int { assume true; 1 }\n");
    assert_eq!(r, refused(&[(1, "word:method"), (2, "word:assume")]));
    assert_eq!(d, vec![]);
}

#[test]
fn a_quote_an_at_and_an_attribute_are_refused_and_a_string_hides_no_word() {
    let (r, d) = scan("function F(): int { 1 }\n@x\nfunction {:axiom} G(): int\n\"a newtype\" x\n\"a\\\"newtype\" y\n");
    assert_eq!(r, refused(&[(2, "@"), (3, "{:"), (4, "\""), (5, "\"")]));
    assert_eq!(d, vec![]);
}

#[test]
fn a_string_ends_at_the_end_of_its_line() {
    let (r, _) = scan("\"abc\nnewtype\"\n");
    assert_eq!(r, refused(&[(1, "\""), (2, "word:newtype"), (2, "\"")]));
}

#[test]
fn a_comment_that_does_not_end_is_refused_at_the_line_where_it_opened() {
    let (r, d) = scan("function F(): int { 1 }\n/* open\n/* inner */\n");
    assert_eq!(r, refused(&[(2, "unclosed")]));
    assert_eq!(d, vec![]);
}

#[test]
fn a_byte_that_is_not_allowed_is_refused_once_for_each_line_and_stops_the_scan() {
    // A carriage return before a line feed is allowed. A lone one is not. The keyword on line 3 is not read.
    let (r, d) = scan("function F(): int { 1 }\r\nfunction \u{e9}(): int { 1 } \u{e9}\n\rmethod\n");
    assert_eq!(r, refused(&[(2, "char"), (3, "char")]));
    assert_eq!(d, vec![]);
}

#[test]
fn a_line_feed_after_a_carriage_return_ends_a_line_and_a_lone_one_at_the_end_is_refused() {
    let (r, d) = scan("function F(): int { 1 }\r\nfunction G(): int { 2 }\r\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![("F".to_string(), 1, false), ("G".to_string(), 2, false)]);
    let (r, _) = scan("function F(): int { 1 }\r");
    assert_eq!(r, refused(&[(1, "char")]));
}

#[test]
fn a_declared_name_of_the_model_is_refused_and_a_comment_does_not_part_it_from_its_word() {
    let (r, d) = scan("function Some(): int { 1 }\nfunction /* c */ v_x(): int { 1 }\npredicate Ok() { true }\nfunction // c\n  trunc_y(): int { 1 }\n");
    assert_eq!(r, refused(&[(1, "name:Some"), (2, "name:v_x"), (5, "name:trunc_y")]));
    assert_eq!(d, vec![]);
}

#[test]
fn a_name_of_the_model_that_is_not_declared_is_no_refusal() {
    let (r, d) = scan("function F(x: int): int { Some(x) }\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![("F".to_string(), 1, false)]);
}

#[test]
fn a_run_of_digits_ends_where_a_letter_starts() {
    let (r, _) = scan("function F(): int { 1newtype }\n");
    assert_eq!(r, refused(&[(1, "word:newtype")]));
}

#[test]
fn a_word_can_hold_a_prime_and_a_question_mark() {
    let (r, d) = scan("function F'?(): int { 1 }\npredicate ?p() { true }\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![("F'?".to_string(), 1, false), ("?p".to_string(), 2, false)]);
}

#[test]
fn a_symbol_between_the_word_and_a_name_parts_them() {
    // `function (` is no declaration, so the word after it declares nothing.
    let (r, d) = scan("function ( Some\nfunction 1 None\n");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![]);
}

#[test]
fn an_empty_file_passes_and_declares_nothing() {
    let (r, d) = scan("");
    assert_eq!(r, refused(&[]));
    assert_eq!(d, vec![]);
}

/// `for` and `array` are keywords of Dafny that are not on the short list of decision 0080, so the scan refuses them. A name
/// that starts with `'` is a name in Dafny, but the scan reads the `'` as a symbol, so such a name is not declared. Each such
/// file is still refused later, so only the words of the refusal differ. The `bvN` types are keywords too. They need a rule for a
/// prefix, and they add no axiom, so the scan lets them through.
#[test]
fn for_and_array_are_refused() {
    let (r, d) = scan("function F(): int { 1 }\nlemma L() { for i := 0 }\nfunction G(a: array<int>): int { 1 }\n");
    assert_eq!(r, refused(&[(2, "word:for"), (3, "word:array")]));
    assert_eq!(d, vec![]);
}

/// Each name of the double model is a name of the model, decisions 0154 and 0159, so a companion file cannot declare one.
#[test]
fn a_name_of_the_double_model_is_refused() {
    let names = ["Double", "abs", "round", "fadd", "fsub", "fmul", "fdiv", "fint", "EPS", "ETA", "MAX", "RoundError", "RoundExactInt"];
    let text: String = names.iter().map(|n| format!("function {n}(): int {{ 1 }}\n")).collect();
    let (r, d) = scan(&text);
    let want: Vec<(u32, String)> = names.iter().enumerate().map(|(i, n)| (i as u32 + 1, format!("name:{n}"))).collect();
    assert_eq!(r, want);
    assert_eq!(d, vec![]);
}

/// Each name of the sort model is a name of the model, decision 0161, so a companion file cannot declare one.
#[test]
fn a_name_of_the_sort_model_is_refused() {
    let names = ["Algorithm", "StdSort", "StrictWeakOrder", "SortedBy"];
    let text: String = names.iter().map(|n| format!("predicate {n}() {{ true }}\n")).collect();
    let (r, d) = scan(&text);
    let want: Vec<(u32, String)> = names.iter().enumerate().map(|(i, n)| (i as u32 + 1, format!("name:{n}"))).collect();
    assert_eq!(r, want);
    assert_eq!(d, vec![]);
}

//! The reader of the output of Dafny in the core, decisions 0068, 0069, 0080, 0083 and 0127. Each test gives the text that Dafny
//! prints and reads the facts, or the verdict.

use cplusp_core::dafny::*;
use cplusp_core::verdict::Verdict;

fn read(text: &str) -> (Reading, Vec<u8>) {
    let bytes = text.as_bytes().to_vec();
    (read_dafny(&bytes), bytes)
}

fn errors(r: &Reading, b: &[u8]) -> Vec<(usize, String)> {
    r.errors.iter().map(|(l, s, e)| (*l, String::from_utf8(b[*s..*e].to_vec()).unwrap())).collect()
}

fn warnings(r: &Reading, b: &[u8]) -> Vec<(usize, String)> {
    r.warnings.iter().map(|(l, s, e)| (*l, String::from_utf8(b[*s..*e].to_vec()).unwrap())).collect()
}

#[test]
fn a_summary_with_two_or_three_counts() {
    assert_eq!(read("Dafny program verifier finished with 5 verified, 0 errors\n").0.summary, Some((5, 0, 0)));
    assert_eq!(read("Dafny program verifier finished with 1 verified, 1 error, 1 time out\n").0.summary, Some((1, 1, 1)));
    assert_eq!(read("Dafny program verifier finished with 0 verified, 2 errors, 3 time outs").0.summary, Some((0, 2, 3)));
}

#[test]
fn a_line_of_another_shape_is_no_summary_and_the_first_summary_counts() {
    let (r, _) = read("Dafny program verifier finished with 5 verified, 0 errors, extra\nDafny program verifier finished with 5 verifieds, 0 errors\nDafny program verifier finished with 2 verified, 1 error\nDafny program verifier finished with 9 verified, 0 errors\n");
    assert_eq!(r.summary, Some((2, 1, 0)));
    assert_eq!(read("Dafny program verifier finished with 18446744073709551616 verified, 0 errors\n").0.summary, None);
    assert_eq!(read("Dafny program verifier finished with -1 verified, 0 errors\n").0.summary, None);
}

#[test]
fn a_file_that_dafny_cannot_read_has_a_summary_of_its_errors() {
    let (r, _) = read("3 resolution/type errors detected in model.dfy\n");
    assert_eq!((r.summary, r.unread), (Some((0, 3, 0)), Some(Unread::Resolve)));
    let (r, _) = read("1 parse errors detected in model.dfy\n");
    assert_eq!((r.summary, r.unread), (Some((0, 1, 0)), Some(Unread::Parse)));
    // A count that cannot be read makes the line no summary.
    assert_eq!(read("x parse errors detected in model.dfy\n").0.summary, None);
}

#[test]
fn error_lines_carry_their_related_lines() {
    let text = "/tmp/a/model.dfy(12,3): Error: assertion might not hold\n/tmp/a/model.dfy(4,1): Related location: this is the postcondition\n/tmp/a/model.dfy(20,5): Error: index out of range\nDafny program verifier finished with 1 verified, 2 errors\n";
    let (r, b) = read(text);
    assert_eq!(errors(&r, &b), vec![(12, "assertion might not hold".to_string()), (20, "index out of range".to_string())]);
    assert_eq!(r.related, vec![(0, 4)]);
    assert_eq!(r.summary, Some((1, 2, 0)));
}

#[test]
fn a_related_line_before_any_error_belongs_to_none() {
    let (r, _) = read("m.dfy(4,1): Related location: x\nm.dfy(5,1): Error: y\n");
    assert_eq!(r.related, vec![]);
    assert_eq!(r.errors.len(), 1);
}

#[test]
fn a_line_number_is_read_as_rust_reads_a_usize() {
    // A plus sign is allowed, and a line with no number or a bad number is no error line.
    let (r, b) = read("m.dfy(+7,1): Error: a\nm.dfy(x,1): Error: b\nm.dfy(7): Error: c\nm.dfy(7,1) : Error: d\n(8,2): Error: e\n");
    assert_eq!(errors(&r, &b), vec![(7, "a".to_string()), (8, "e".to_string())]);
}

#[test]
fn the_first_kind_marker_splits_the_line() {
    let (r, b) = read("m.dfy(3,1): Error: x: Error: y\n");
    assert_eq!(errors(&r, &b), vec![(3, "x: Error: y".to_string())]);
}

#[test]
fn a_carriage_return_before_a_line_feed_is_no_part_of_the_line_and_white_space_ends_a_summary() {
    let (r, b) = read("m.dfy(3,1): Error: x\r\nDafny program verifier finished with 4 verified, 1 error  \t\r\n");
    assert_eq!(errors(&r, &b), vec![(3, "x".to_string())]);
    assert_eq!(r.summary, Some((4, 1, 0)));
}

#[test]
fn warnings_are_read_with_their_lines() {
    let (r, b) = read(
        "m.dfy(9,1): Warning: this forall statement has no body\nm.dfy(10,2): Warning: Could not find a trigger for this quantifier\n",
    );
    assert_eq!(
        warnings(&r, &b),
        vec![(9, "this forall statement has no body".to_string()), (10, "Could not find a trigger for this quantifier".to_string())]
    );
}

/// The companion file is the lines from index 7 up to 10 of the Dafny text, so Dafny lines 8 to 10, and line 11 just past it.
fn judged(text: &str, exit_ok: bool, refused: bool, methods: usize) -> Verdict {
    let (r, _) = read(text);
    judge(&r, exit_ok, refused, methods, 7, 10)
}

#[test]
fn proved_needs_a_clean_summary_and_every_method() {
    let ok = "Dafny program verifier finished with 3 verified, 0 errors\n";
    assert_eq!(judged(ok, true, false, 3), Verdict::Proved);
    assert_eq!(judged(ok, true, false, 4), Verdict::NotProved);
    assert_eq!(judged(ok, true, true, 3), Verdict::NotProved);
    assert_eq!(judged(ok, false, false, 3), Verdict::ToolFailed);
    assert_eq!(judged("no summary at all\n", true, false, 0), Verdict::ToolFailed);
}

#[test]
fn a_warning_on_the_companion_file_is_an_axiom_except_a_missing_trigger() {
    let tail = "Dafny program verifier finished with 3 verified, 0 errors\n";
    assert_eq!(judged(&format!("m.dfy(9,1): Warning: a bodyless function\n{tail}"), true, false, 3), Verdict::NotProved);
    assert_eq!(
        judged(&format!("m.dfy(9,1): Warning: Could not find a trigger for this quantifier\n{tail}"), true, false, 3),
        Verdict::Proved
    );
    // Outside the companion file, before it and after it.
    assert_eq!(judged(&format!("m.dfy(7,1): Warning: x\nm.dfy(11,1): Warning: y\n{tail}"), true, false, 3), Verdict::Proved);
}

#[test]
fn a_parse_error_is_the_authors_only_when_each_error_is_in_the_companion_file() {
    // Line 11 is one past the last line of the companion file, and counts as the companion file, decision 0083.
    assert_eq!(
        judged("m.dfy(9,1): Error: a\nm.dfy(11,1): Error: b\n2 parse errors detected in m.dfy\n", false, false, 3),
        Verdict::NotProved
    );
    assert_eq!(
        judged("m.dfy(9,1): Error: a\nm.dfy(2,1): Error: b\n2 parse errors detected in m.dfy\n", false, false, 3),
        Verdict::ToolFailed
    );
    assert_eq!(judged("1 parse errors detected in m.dfy\n", false, false, 3), Verdict::ToolFailed);
    // A resolution error anywhere is the author's.
    assert_eq!(judged("m.dfy(2,1): Error: a\n1 resolution/type errors detected in m.dfy\n", false, false, 3), Verdict::NotProved);
}

#[test]
fn with_no_companion_file_no_line_is_in_it() {
    let (r, _) = read("m.dfy(1,1): Error: a\n1 parse errors detected in m.dfy\n");
    assert_eq!(judge(&r, false, false, 3, 0, 0), Verdict::ToolFailed);
}

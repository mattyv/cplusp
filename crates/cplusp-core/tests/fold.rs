//! The fold of named constants and enumerators in a contract, decisions 0106, 0109 and 0124. The names are ids, as the shell
//! gives them.

use cplusp_core::fold::*;
use cplusp_core::model::{BinOp, Tok};

const A: u32 = 1;
const B: u32 = 2;
const N: u32 = 3;
const M: u32 = 4;
const I: u32 = 5;
const KIND: u32 = 10;
const SMALL: u32 = 11;
const LARGE: u32 = 12;
const OTHER: u32 = 13;

fn run(toks: &[Tok], constants: &[(u32, i128)], shadow: &[u32], enums: &[(u32, u32)], enumerators: &[(u32, u32)]) -> Vec<Tok> {
    let t = Folds { constants: constants.to_vec(), shadow: shadow.to_vec(), enums: enums.to_vec(), enumerators: enumerators.to_vec() };
    fold(&toks.to_vec(), &t)
}

#[test]
fn a_constant_reads_as_its_value_and_a_negative_one_in_parentheses() {
    let out = run(&[Tok::Ident(N), Tok::Op(BinOp::Add), Tok::Ident(M)], &[(N, 7), (M, -3)], &[], &[], &[]);
    assert_eq!(out, vec![Tok::Int(7), Tok::Op(BinOp::Add), Tok::LParen, Tok::Op(BinOp::Sub), Tok::Int(3), Tok::RParen]);
}

#[test]
fn the_most_negative_constant_has_its_exact_magnitude() {
    let out = run(&[Tok::Ident(N)], &[(N, i64::MIN as i128)], &[], &[], &[]);
    assert_eq!(out, vec![Tok::LParen, Tok::Op(BinOp::Sub), Tok::Int(1u64 << 63), Tok::RParen]);
}

/// A constant holds the full range of uint64_t, decision 0063. A magnitude above it does not fold, and the name stays.
#[test]
fn a_constant_up_to_the_largest_u64_folds_and_a_larger_one_stays_a_name() {
    let out = run(&[Tok::Ident(N), Tok::Ident(M), Tok::Ident(I)], &[(N, u64::MAX as i128), (M, -(u64::MAX as i128)), (I, (u64::MAX as i128) + 1)], &[], &[], &[]);
    assert_eq!(out, vec![Tok::Int(u64::MAX), Tok::LParen, Tok::Op(BinOp::Sub), Tok::Int(u64::MAX), Tok::RParen, Tok::Ident(I)]);
}

#[test]
fn a_parameter_or_local_hides_the_constant() {
    let out = run(&[Tok::Ident(N)], &[(N, 7)], &[N], &[], &[]);
    assert_eq!(out, vec![Tok::Ident(N)]);
}

#[test]
fn a_bound_name_hides_the_constant_on_the_whole_line() {
    // `N + forall N, M :: N` keeps each N and M.
    let toks = [Tok::Ident(N), Tok::Op(BinOp::Add), Tok::Forall, Tok::Ident(N), Tok::Comma, Tok::Ident(M), Tok::ColonColon, Tok::Ident(N)];
    let out = run(&toks, &[(N, 7), (M, 8)], &[], &[], &[]);
    assert_eq!(out, toks.to_vec());
}

#[test]
fn a_call_and_a_path_keep_the_name() {
    let toks = [Tok::Ident(N), Tok::LParen, Tok::RParen, Tok::Ident(A), Tok::ColonColon, Tok::Ident(N), Tok::Ident(N), Tok::ColonColon, Tok::Ident(B)];
    let out = run(&toks, &[(N, 7)], &[], &[], &[]);
    assert_eq!(out, toks.to_vec());
}

#[test]
fn the_first_constant_of_a_name_wins() {
    let out = run(&[Tok::Ident(N)], &[(N, 7), (N, 9)], &[], &[], &[]);
    assert_eq!(out, vec![Tok::Int(7)]);
}

#[test]
fn an_enumerator_of_one_enum_reads_as_its_index() {
    let toks = [Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(LARGE), Tok::Op(BinOp::Eq), Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(SMALL)];
    let out = run(&toks, &[], &[], &[(KIND, 40)], &[(40, SMALL), (40, LARGE)]);
    assert_eq!(out, vec![Tok::Enumerator(40, 1), Tok::Op(BinOp::Eq), Tok::Enumerator(40, 0)]);
}

#[test]
fn an_enum_name_two_enums_share_bound_names_and_other_members_stay() {
    let toks = [Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(SMALL)];
    // Two enums of the name.
    assert_eq!(run(&toks, &[], &[], &[(KIND, 40), (KIND, 41)], &[(40, SMALL), (41, SMALL)]), toks.to_vec());
    // A member that is not an enumerator of it.
    assert_eq!(run(&[Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(OTHER)], &[], &[], &[(KIND, 40)], &[(40, SMALL)]), vec![Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(OTHER)]);
    // A name that a quantifier binds.
    let bound = [Tok::Exists, Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(SMALL)];
    assert_eq!(run(&bound, &[], &[], &[(KIND, 40)], &[(40, SMALL)]), bound.to_vec());
}

#[test]
fn an_enum_with_no_enumerators_still_counts_as_an_enum_of_the_name() {
    let toks = [Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(SMALL)];
    assert_eq!(run(&toks, &[], &[], &[(KIND, 40), (KIND, 41)], &[(41, SMALL)]), toks.to_vec());
}

#[test]
fn a_constant_next_to_a_folded_enumerator_is_read_after_the_fold() {
    // `Kind::Small + I`: the enumerator folds first, and I is no longer next to `::`.
    let toks = [Tok::Ident(KIND), Tok::ColonColon, Tok::Ident(SMALL), Tok::Op(BinOp::Add), Tok::Ident(I)];
    let out = run(&toks, &[(I, 2), (SMALL, 5)], &[], &[(KIND, 40)], &[(40, SMALL)]);
    assert_eq!(out, vec![Tok::Enumerator(40, 0), Tok::Op(BinOp::Add), Tok::Int(2)]);
}

#[test]
fn no_constant_and_no_enum_changes_nothing() {
    let toks = [Tok::Ident(A), Tok::Op(BinOp::Lt), Tok::Int(3), Tok::ColonColon, Tok::Result];
    assert_eq!(run(&toks, &[], &[], &[], &[]), toks.to_vec());
}

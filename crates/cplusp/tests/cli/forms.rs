use super::*;

/// int8_t, int16_t and uint16_t, a right shift of an unsigned and of a negative signed value, a named constexpr constant in code
/// and in a contract, and a character in a contract, prove, decision 0106. Each constant has its true value, decision 0107.
#[test]
fn small_forms_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A narrowing to int8_t that may not fit, a shift whose amount may be negative or too wide, and a contract that a constant does
/// not meet, are named at their lines, decisions 0106 and 0107.
#[test]
fn prove_names_a_narrowing_and_a_shift_that_may_fail() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let shift = "the shift amount may be negative or not below the width of the type.";
    let mut wants = vec!["model-small-wrong.cpp:4: the value may not fit int8_t.".to_string()];
    wants.extend([8, 14].map(|line| format!("model-small-wrong.cpp:{line}: {shift}")));
    // Each wrong value of a constant, and the field that hides a constant of the file, decision 0107.
    wants.extend([25, 30, 35, 40, 50].map(|line| format!("model-small-wrong.cpp:{line}: the ensures line may not hold on this return.")));
    for want in &wants {
        assert!(failed.iter().any(|l| l.ends_with(want.as_str())), "{want}: {text}");
    }
    assert_eq!(failed.len(), wants.len(), "{text}");
}

/// A static member, a namespace constant, an unnamed namespace and a local constant of an enclosing function hide a constant of the
/// file with the same name, and so does a name with two meanings. The name in the contract is no constant then, decision 0107.
#[test]
fn a_constant_that_cpp_does_not_find_from_the_function_is_no_constant() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-small-hidden.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let wants = [
        "model-small-hidden.cpp:14: kScale in the contract is no parameter.",
        "model-small-hidden.cpp:22: k in the contract is no parameter.",
        "model-small-hidden.cpp:32: j in the contract is no parameter.",
        "model-small-hidden.cpp:44: k in the contract is no parameter.",
        "model-small-hidden.cpp:56: m in the contract is no parameter.",
        "model-small-hidden.cpp:66: n in the contract is no parameter.",
    ];
    for want in wants {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), wants.len(), "{text}");
}

/// A variable that is not constexpr is no constant of a contract, and a left shift has no rule, decision 0106.
#[test]
fn a_variable_in_a_contract_and_a_left_shift_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-small-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in ["model-small-refuse.cpp:6: scale in the contract is no parameter.", "model-small-refuse.cpp:12: BinaryOperator <<: the translator has no rule for it yet."] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// A reference parameter on the modifies line takes a value in and gives it back. A caller writes back a local or its own
/// reference parameter, and a trusted function can write one, decision 0108.
#[test]
fn reference_parameters_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An ensures line about a reference parameter that the body does not meet, a call that does not meet a requires line, and a caller
/// that reads a local as it was before a call that wrote it, are named at their lines, decision 0108.
#[test]
fn prove_names_a_reference_parameter_that_does_not_meet_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-ref-wrong.cpp:6: the ensures line may not hold on this return.",
        "model-ref-wrong.cpp:19: a requires line of the callee may not hold.",
        "model-ref-wrong.cpp:33: the ensures line may not hold on this return.",
        "model-ref-wrong.cpp:40: the ensures line may not hold on this return.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 4, "{text}");
}

/// A name on the modifies line that is no reference parameter, a reference parameter that the line does not name, and a call that
/// writes back to a parameter by value or to a field, are refused at their lines, decision 0108. A modifies line of another form is
/// refused first, and a name with parts is a name, decision 0110.
#[test]
fn a_modifies_line_and_a_write_back_with_no_rule_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-ref-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-ref-refuse.cpp:10: n on the modifies line is no reference parameter.",
        "model-ref-refuse.cpp:15: x is a reference parameter that the modifies line does not name.",
        "model-ref-refuse.cpp:25: y is a parameter. The translator writes only a local or a reference parameter.",
        "model-ref-refuse.cpp:30: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
        "model-ref-refuse.cpp:35: the contract line has a form the translator cannot read.",
        "model-ref-refuse.cpp:40: Tally::count_ on the modifies line is no reference parameter.",
        "model-ref-refuse.cpp:48: BinaryOperator <<=: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 7, "{text}");
}

/// A function whose body is refused keeps a header with the values it gives back, so Dafny resolves each call of it, decision 0108.
#[test]
fn a_caller_of_a_refused_function_that_writes_a_reference_resolves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    assert!(!text.lines().any(|l| l.starts_with("Not proved: ")), "{text}");
}

/// An enum class is a datatype, and a switch over it is a match: a case that returns, a case that ends with a break, a nested switch,
/// an enum in a struct and in a contract, decision 0109. An enum named only by its enumerators, a switch through a const reference,
/// and case bodies in braces, decision 0114.
#[test]
fn enums_and_switches_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-enum.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A case that does not meet the contract, and a value of an enum that a branch may not change, are named at their lines, decision
/// 0109.
#[test]
fn prove_names_a_switch_that_does_not_meet_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-enum-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-enum-wrong.cpp:12: the ensures line may not hold on this return.", "model-enum-wrong.cpp:23: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A marked fall, a default, a break in another place, an enum with values written, a cast of an enum and an order of enums are
/// refused at their lines, decision 0109. So are an order of enums in a contract, an enumerator of two enums with one plain name,
/// and an enumerator whose name Dafny cannot read, decision 0114.
#[test]
fn switches_and_enums_with_no_rule_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-enum-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let wants = [
        "model-enum-refuse.cpp:14: AttributedStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:27: DefaultStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:36: BreakStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:47: Flag: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:52: CXXStaticCastExpr IntegralCast: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:56: BinaryOperator <: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:60: the contract line has a form the translator cannot read.",
        "model-enum-refuse.cpp:73: the contract line has a form the translator cannot read.",
        "model-enum-refuse.cpp:79: P$: a name with a character Dafny cannot read.",
    ];
    for want in wants {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), wants.len(), "{text}");
}

/// A std::byte that the file declares itself is no view as bytes, so a read through it is a pun, decision 0117. Only the std::byte of
/// the system header is exempt from the row type_punning.
#[test]
fn a_byte_that_the_file_declares_is_no_view_as_bytes() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("punning-own-byte.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [("type_punning".to_string(), 12)].into_iter().collect();
    assert_eq!(reported, expected, "{out}");
}

/// A raw copy tells the bot why the gate refuses it, decision 0120. The sentence of the plugin follows the message of the row.
#[test]
fn a_raw_copy_says_why_it_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let banned = root().join("rules/type_punning/banned.cpp");
    let o = gated(&[banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let wants = [
        (154, "The copy reads padding into a type that is not bytes."),
        (162, "The copy writes a type that holds a pointer, a reference, an enum or a bool."),
        (194, "The copy writes to a place of unknown type."),
        (260, "The copy writes to a place of unknown type."),
        (276, "The copy writes a type that holds a pointer, a reference, an enum or a bool."),
        (297, "The copy reads a place of unknown type into a type that is not bytes."),
        (324, "The copy writes to a place of unknown type."),
        (331, "The copy writes to a place of unknown type."),
    ];
    for (line, want) in wants {
        let at = format!("banned.cpp:{line}: ");
        assert!(out.lines().any(|l| l.contains(&at) && l.ends_with(&format!("Use std::bit_cast for the bits of a value, or a pointer to bytes. {want}"))), "{line}: {out}");
    }
}

/// A refused character that the eye cannot see is named by its code point, decision 0125. The sentence for a no-break space is
/// not a quoted space.
#[test]
fn an_invisible_character_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-invisible.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 1, "{text}");
    assert!(refusals[0].ends_with("model-invisible.cpp:4: U+00A0 in a contract: the translator has no rule for it yet."), "{text}");
}

/// A format character, such as a zero-width space or a right-to-left override, is named by its code point too, decision 0126.
#[test]
fn a_format_character_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-format-char.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 2, "{text}");
    assert!(refusals[0].ends_with("model-format-char.cpp:4: U+200B in a contract: the translator has no rule for it yet."), "{text}");
    assert!(refusals[1].ends_with("model-format-char.cpp:9: U+202E in a contract: the translator has no rule for it yet."), "{text}");
}

/// A Hangul filler is a letter that prints as nothing, so it is named by its code point too, decision 0126.
#[test]
fn a_hangul_filler_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-filler.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 1, "{text}");
    assert!(refusals[0].ends_with("model-filler.cpp:4: U+3164 in a contract: the translator has no rule for it yet."), "{text}");
}

/// A chain of three comparisons means each of them, and `*o` reads an optional, decision 0131. The ensures lines need the last
/// comparison of each chain, and the first and the last index of the sorted form.
#[test]
fn a_longer_chain_and_the_star_of_an_optional_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-chain.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// The chain gives no more than it says, and `*result` with no test of has_value does not prove, decision 0131.
#[test]
fn a_longer_chain_gives_no_more_and_the_star_needs_a_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-chain-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-chain-wrong.cpp:8: the ensures line may not hold on this return.", "model-chain-wrong.cpp:12: the optional may be empty or the pointer may be null here."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A chain with two directions anywhere in it, and `*` on a value that is not an optional, are refused, decision 0131.
#[test]
fn a_chain_that_turns_and_the_star_of_a_scalar_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-chain-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(
        refusals.iter().map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["4: the contract line has a form the translator cannot read.", "10: the contract line has a form the translator cannot read."],
        "{text}"
    );
}

/// A const std::array is a read-only sequence of fixed length, decision 0132: by reference and by value.
#[test]
fn a_const_array_is_a_sequence_of_fixed_length() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-array.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-array-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["8: the index may be out of range."],
        "{text}"
    );
}

/// An array with no const, a struct with an array field, and an array of bool stay out of the subset, decisions 0132 and 0136.
#[test]
fn an_array_with_no_const_and_an_array_field_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-array-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec![
            "6: std::array<int32_t, 4> &: the translator has no rule for it yet.",
            "23: an optional of a struct or a sequence of bool has no rule yet.",
        ],
        "{text}"
    );
}

/// has_value, value and the star read the optional that a call gives, decision 0133. A read of a value that may be missing does
/// not prove.
#[test]
fn an_optional_that_a_call_gives_is_read_through_its_temporary() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-temp-opt.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-temp-opt-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["15: the optional may be empty or the pointer may be null here."],
        "{text}"
    );
}

/// An optional of a plain struct, and `->` in code and in a contract, decision 0137.
#[test]
fn an_optional_of_a_struct_and_the_arrow_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-opt-struct.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A read through `->` of an optional that may be empty does not prove, in code and in a contract, decision 0137.
#[test]
fn the_arrow_needs_a_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-opt-struct-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-opt-struct-wrong.cpp:20: the optional may be empty or the pointer may be null here.", "model-opt-struct-wrong.cpp:23: the optional may be empty or the pointer may be null here."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// An optional of a struct that holds a sequence stays out, decision 0137.
#[test]
fn an_optional_of_a_struct_that_holds_a_sequence_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-opt-struct-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["11: a struct that holds a sequence has no rule yet in an optional, a pointer, a unique_ptr, or a vector that the code makes or writes."],
        "{text}"
    );
}

/// int8_t, int16_t and uint16_t fields of a plain struct, decision 0138. A value that may not fit the field does not prove.
#[test]
fn small_integer_types_can_be_fields() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small-fields.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-small-fields-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["10: the value may not fit uint16_t."],
        "{text}"
    );
}

/// `at` of a read-only sequence is an index, decision 0139. An index that may be out of range does not prove.
#[test]
fn at_is_an_index() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-at.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-at-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["7: the index may be out of range."],
        "{text}"
    );
}

/// A pointer to const is an optional, decision 0140: `*p`, `p->f`, `p == nullptr` and `p != nullptr`, in code and in a contract, and
/// the arguments `&x`, `nullptr` and a pointer parameter.
#[test]
fn a_pointer_to_const_is_an_optional() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pointer.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A read through a pointer that may be null does not prove, in code and in a contract, and a caller must meet `p != nullptr`,
/// decision 0140.
#[test]
fn a_pointer_that_may_be_null_does_not_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pointer-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in [
        "model-pointer-wrong.cpp:5: the optional may be empty or the pointer may be null here.",
        "model-pointer-wrong.cpp:8: the optional may be empty or the pointer may be null here.",
        "model-pointer-wrong.cpp:19: a requires line of the callee may not hold.",
    ] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A pointer with no const, and a pointer tested as a bool, have no rule yet, decision 0140. Two pointers do not compare, in code
/// and in a contract, and neither does `this`, decision 0141. No refusal speaks in the words of Dafny.
#[test]
fn a_pointer_with_no_const_and_a_pointer_as_a_bool_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-pointer-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 6, "{text}");
    assert_eq!(refusals[0], "5: int32_t *: the translator has no rule for it yet.", "{text}");
    for (i, line) in [(1, "10: "), (2, "18: "), (5, "34: ")] {
        assert!(refusals[i].starts_with(line) && refusals[i].ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
    assert_eq!(refusals[3], "21: the contract line has a form the translator cannot read.", "{text}");
    assert_eq!(refusals[4], "26: the contract line has a form the translator cannot read.", "{text}");
}

/// A unique_ptr that the code only reads is an optional, decision 0142: a const reference parameter, a result, a local that a call
/// sets, std::make_unique, `*p`, `p->f` and the test against nullptr.
#[test]
fn a_unique_ptr_that_is_only_read_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-unique-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["12: the optional may be empty or the pointer may be null here."],
        "{text}"
    );
}

/// A write through a unique_ptr, a move, a unique_ptr by value or by reference with no const, and two unique_ptrs compared, have no
/// rule, decision 0142.
#[test]
fn a_unique_ptr_that_is_written_or_compared_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-unique-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 4, "{text}");
    for (r, line) in refusals.iter().zip(["8: ", "12: ", "17: ", "22: "]) {
        assert!(r.starts_with(line) && r.ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
}

/// A range-for is a loop over indexes, and an index line names the index, decision 0143. A loop with no index line proves too.
#[test]
fn a_range_for_is_a_loop_over_indexes() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-range.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-range-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-range-wrong.cpp:10: the invariant may not hold when the loop starts.", "model-range-wrong.cpp:22: the value may not fit int32_t."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// An index line above another loop or above a function, an index name that the function has, and an index line with two names,
/// are refused, decision 0143. So are an index named as a field or a constant, and a structured binding, decision 0144.
#[test]
fn an_index_line_in_the_wrong_place_or_with_a_used_name_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-range-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let wrong_place = "a contract line in the wrong place. A requires, an ensures, a modifies or a decreases line goes above a function. An invariant or a decreases line goes above a loop, and an index line above a range-for.";
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1.to_string()).collect::<Vec<_>>(),
        vec![
            format!("8: {wrong_place}"),
            "17: i on the index line is a name the function already has.".to_string(),
            "26: the contract line has a form the translator cannot read.".to_string(),
            format!("33: {wrong_place}"),
            "43: count on the index line is a name the function already has.".to_string(),
            "55: N on the index line is a name the function already has.".to_string(),
            "70: CXXForRangeStmt: the translator has no rule for it yet.".to_string(),
        ],
        "{text}"
    );
}

/// A vector by reference that the function writes takes its value in and gives it back, decision 0145: element writes, reads,
/// and a loop that writes each element.
#[test]
fn a_vector_by_reference_that_the_function_writes_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-ref.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-ref-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 2, "{text}");
    assert_eq!(failed[0], "8: the index may be out of range.", "{text}");
    assert!(failed[1].ends_with(": the ensures line may not hold on this return."), "{text}");
}

/// A vector by reference that the modifies line does not name, clear, a compound write, a vector of bool and a call that
/// passes the vector on are refused, decisions 0145, 0147 and 0148.
#[test]
fn a_vector_by_reference_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-vec-ref-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 5, "{text}");
    assert_eq!(refusals[0], "7: v is a reference parameter that the modifies line does not name.", "{text}");
    for (r, line) in refusals[1..4].iter().zip(["12: ", "18: ", "22: "]) {
        assert!(r.starts_with(line) && r.ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
    // The call passes the vector on, decision 0147.
    assert_eq!(refusals[4], "34: v is a vector by reference. A call that passes it on has no rule yet.", "{text}");
}

/// push_back adds one element at the end of a vector by reference, and Dafny checks each index and the length after, decision
/// 0148.
#[test]
fn push_back_grows_a_vector_by_reference() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-push.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-push-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 2, "{text}");
    assert_eq!(failed[0], "10: the index may be out of range.", "{text}");
    assert!(failed[1].ends_with(": the ensures line may not hold on this return."), "{text}");
}

/// The example sorted_insert proves with push_back, its loop invariants and its companion file, decision 0148.
#[test]
fn the_sorted_insert_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/sorted_insert/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// count_if with a lambda written in the call proves against a companion count that says the same test, decision 0149. A lambda
/// with another test fails its ensures line, and a count with no bound fails the int64 fit and the int32 fit at line 14.
#[test]
fn count_if_with_a_lambda_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-count-if.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-count-if-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 3, "{text}");
    assert!(failed[0].starts_with("9: ") && failed[0].ends_with(": the ensures line may not hold on this return."), "{text}");
    assert_eq!(failed[1], "14: the value may not fit int64_t.", "{text}");
    assert_eq!(failed[2], "14: the value may not fit int32_t.", "{text}");
}

/// Another algorithm, an init capture and a lambda body of two statements are refused at their lines, and the lambda is no
/// function of its own, decision 0149.
#[test]
fn count_if_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-count-if-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let mut lines: Vec<&str> = refusals.iter().map(|r| r.split(':').next().unwrap()).collect();
    lines.dedup();
    assert_eq!(lines, ["7", "11", "15", "22", "26"], "{text}");
    assert!(!text.contains("CXXMethodDecl"), "{text}");
    // A count_if that misses the rule names the limit that it misses, and only that, decision 0157.
    let no_rule = ": the translator has no rule for it yet.";
    for (line, what) in [
        ("11", "count_if with an init capture in its lambda"),
        ("15", "count_if with a lambda whose body is more than one return"),
        ("22", "count_if over a range other than v.begin(), v.end() of one sequence parameter"),
        ("26", "count_if with a lambda whose parameter is not the element type"),
    ] {
        let at: Vec<&&str> = refusals.iter().filter(|r| r.split(':').next() == Some(line)).collect();
        assert_eq!(at, [&format!("{line}: {what}{no_rule}").as_str()], "{line}: {text}");
    }
}

/// The example lambdas proves with count_if and its companion file, decision 0149.
#[test]
fn the_lambdas_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/lambdas/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

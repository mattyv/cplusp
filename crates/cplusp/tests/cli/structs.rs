use super::*;

/// A struct of scalars is a Dafny datatype, decision 0073. Field reads, braced values, nested structs and a copy to a parameter prove.
#[test]
fn structs_of_scalars_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-struct.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each struct with no rule is refused at its line, decision 0073.
#[test]
fn structs_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-struct-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, expected) in [
        (8, "Handle: the translator has no rule for it yet."),
        (18, "BinaryOperator =: the translator has no rule for it yet."),
        (22, "z in the contract is no field of the struct."),
        (28, "ImplicitValueInitExpr: the translator has no rule for it yet."),
        (33, "p is a reference parameter that the modifies line does not name."),
    ] {
        let want = format!("model-struct-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 5, "{text}");
}

/// A destructor and an operator() of a plain struct have models. Their names reach the Dafny text as words, never as the C++
/// spelling, decisions 0069 and 0178.
#[test]
fn a_member_function_reaches_the_dafny_text_as_a_word_whatever_its_name() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-member-names.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Not provable: "), "{text}");
    let dafny = std::fs::read_to_string(out).unwrap();
    assert!(dafny.contains("method c_D'dtor(") && dafny.contains("method c_D'call("), "{dafny}");
    assert!(!dafny.contains('~'), "{dafny}");
}

/// An optional scalar is a Dafny Option, decision 0075. Its reads in code and contracts, `std::nullopt`, the construction from a
/// value, a field, a copy and a call prove.
#[test]
fn optional_scalars_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-optional.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each read of an optional that may be empty is named at its line, in code and in a contract, decision 0075.
#[test]
fn prove_names_each_read_of_an_optional_that_may_be_empty() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-optional-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for line in [6, 9, 18] {
        let want = format!("model-optional-wrong.cpp:{line}: the optional may be empty or the pointer may be null here.");
        assert!(failed.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    // The ensures line reads the value of the empty optional that line 12 gives, so it cannot hold on that return either.
    let want = "model-optional-wrong.cpp:12: the ensures line may not hold on this return.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    // A value that the compiler turns into an optional is checked like any other value.
    let want = "model-optional-wrong.cpp:22: the value may not fit int32_t.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(failed.len(), 5, "{text}");
}

/// Each use of an optional with no rule is refused at its line, decision 0075. A construction from an expression of type
/// `std::nullopt_t` that is not `std::nullopt` itself is refused, so its argument cannot vanish from the model. An optional of a plain
/// struct has a rule since decision 0137, so `of_struct` is no longer refused.
#[test]
fn optionals_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-optional-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, expected) in [
        (6, "ImplicitCastExpr UserDefinedConversion: the translator has no rule for it yet."),
        (14, "CXXOperatorCallExpr: the translator has no rule for it yet."),
        (19, "CXXOperatorCallExpr: the translator has no rule for it yet."),
        (35, "CXXConstructExpr: the translator has no rule for it yet."),
        (39, "CXXConstructExpr: the translator has no rule for it yet."),
        (43, "a sequence or an optional made from one of another type or length."),
    ] {
        let want = format!("model-optional-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
}

/// A struct that holds a sequence, a recursive struct and a sequence of structs prove, decision 0076. Reads on a field or an
/// element, contracts on a path, a loop over the children and a recursion into a child.
#[test]
fn structs_that_hold_sequences_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-nodes.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each index into a nested sequence and a recursion that does not go down are named at their lines, decision 0076.
#[test]
fn prove_names_each_failed_read_and_measure_on_a_recursive_struct() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-nodes-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let index = "model-nodes-wrong.cpp:11: the index may be out of range.";
    assert_eq!(failed.iter().filter(|l| l.ends_with(index)).count(), 2, "{text}");
    let measure = "model-nodes-wrong.cpp:16: the decreases line may not decrease at this call.";
    assert!(failed.iter().any(|l| l.ends_with(measure)), "{text}");
    assert_eq!(failed.len(), 3, "{text}");
}

/// A struct that holds a sequence, directly or through a field, is a value: a local copy, a result and a copy of a struct around
/// it translate, decision 0187.
#[test]
fn a_struct_that_holds_a_sequence_is_a_value() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-nodes-value.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.lines().any(|l| l.starts_with("Not provable: ")), "{text}");
}

/// A struct or a field whose name Dafny cannot read is refused at the struct's line, as a function is, decision 0069. Found by the
/// review of decision 0076.
#[test]
fn a_struct_or_field_name_dafny_cannot_read_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-struct-names.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, name) in [(5, "a$b"), (10, "N$")] {
        let want = format!("model-struct-names.cpp:{line}: {name}: a name with a character Dafny cannot read.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// `empty()` and `subspan(k)` prove, in code and in contracts, through a recursion over a span, decision 0078.
#[test]
fn subspan_and_empty_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-subspan.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An offset past the end of a span is named at its line, decision 0078.
#[test]
fn prove_names_an_offset_that_may_be_past_the_end() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-subspan-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let want = "model-subspan-wrong.cpp:17: the offset may be past the end.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(failed.len(), 1, "{text}");
}

/// The forms of a span with no rule yet are refused at their lines, decision 0078.
#[test]
fn spans_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-subspan-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for line in [11, 16] {
        let want = format!("model-subspan-refuse.cpp:{line}: CXXMemberCallExpr: the translator has no rule for it yet.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// A contract calls the functions and predicates of the companion file, decision 0079: an integer function, a predicate on a
/// recursive struct, and a predicate in a requires line.
#[test]
fn specification_functions_from_the_companion_file_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A function with no body and an ensures line in the companion file is an axiom. Dafny proves a wrong body from it, and the run
/// must not say proved, decision 0079.
#[test]
fn prove_refuses_an_axiom_in_the_companion_file() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-axiom.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-axiom.spec.dfy:3: a function with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A call to a name that the companion file does not declare is refused at the contract line, decision 0079.
#[test]
fn a_call_to_a_name_the_companion_file_does_not_declare_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-spec-name.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let want = "model-spec-name.cpp:4: Min is no function of the companion file.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 1, "{text}");
}

/// A companion file that holds an attribute, a method or an assume is refused at each word, and then it declares no function,
/// decisions 0079 and 0099.
#[test]
fn a_companion_file_with_other_words_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-spec-words.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (file, line, word) in [("model-spec-words.spec.dfy", 1, "{:"), ("model-spec-words.spec.dfy", 3, "method"), ("model-spec-words.spec.dfy", 6, "assume")] {
        let want = format!("{file}:{line}: {word}: a companion file can hold only functions, predicates and lemmas.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    let want = "model-spec-words.cpp:4: Max is no function of the companion file.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 4, "{text}");
}

/// A struct refused for its name leaves no method that names it, so prove ends with the refusals and does not fail on the Dafny
/// text. Found after decision 0078.
#[test]
fn prove_stops_at_the_refusal_of_a_struct_name() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-struct-names.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
}

/// The thin slice, decision 0056: radix_find proves end to end. Gate, translator and Dafny, from C++ with a contract and a companion
/// file of specification functions. The height bound is the rule of the battery case stack_depth.
#[test]
fn radix_find_proves_end_to_end() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-radix.cpp", &["--time-limit", "60"], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// The four companion files from the review of decision 0079 each made a wrong body prove. Each is now refused at the word that
/// hides an axiom or the model, and no run says proved, decision 0080.
#[test]
fn prove_refuses_each_companion_file_that_hid_an_axiom_or_the_model() {
    let dafny = dafny();
    require_clang_tidy();
    let word = |w: &str| format!("{w}: a companion file can hold only functions, predicates and lemmas.");
    let cases: [(&str, Vec<(u32, String)>); 4] = [
        ("unclosed", vec![(2, "a comment that does not end.".to_string())]),
        ("string", vec![(1, word("\"")), (2, word("{:"))]),
        ("nested", vec![(2, word("type")), (2, word("witness"))]),
        ("newtype", vec![(1, word("newtype")), (1, word("witness"))]),
    ];
    for (name, wants) in cases {
        let o = prove(&format!("model-spec-{name}.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert!(!text.contains("ok: proved"), "{name}: {text}");
        for (line, sentence) in wants {
            let want = format!("model-spec-{name}.spec.dfy:{line}: {sentence}");
            assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(&want)), "{want}: {text}");
        }
    }
}

/// A contract call that Dafny cannot resolve is named at its C++ line in the words of Dafny, and the run is not proved, with
/// exit 1. It is no failure of the tool, decision 0080.
#[test]
fn prove_names_a_resolution_error_at_its_line() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-arity.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-arity.cpp:3: Dafny says: wrong number of arguments";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.contains(want)), "{want}: {text}");
}

/// Two companion files from the second review made a wrong body prove: a lone carriage return hid an axiom from the scan, and a
/// function named Some changed the model's Some. Both are refused, and neither proves, decision 0083.
#[test]
fn prove_refuses_a_lone_carriage_return_and_a_name_of_the_model() {
    let dafny = dafny();
    require_clang_tidy();
    for (name, want) in [
        ("cr", "model-spec-cr.spec.dfy:1: a character that a companion file cannot hold."),
        ("some", "model-spec-some.spec.dfy:1: Some: a name that the model uses."),
    ] {
        let o = prove(&format!("model-spec-{name}.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert!(!text.contains("ok: proved"), "{name}: {text}");
        assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A parse error in the companion file is the author's, named in its file in the words of Dafny, with exit 1, decision 0083.
#[test]
fn prove_names_a_parse_error_in_the_companion_file() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-brace.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-brace.spec.dfy:2: Dafny says: rbrace expected.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// When Dafny verifies fewer items than the model has methods, and nothing else is wrong, prove says so in one line, decision 0083.
#[test]
fn prove_names_a_run_that_verified_too_few_items() {
    dafny();
    require_clang_tidy();
    let o = prove("model-clamp.cpp", &[], &fixture("fake-dafny-few-verified.sh"));
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-clamp.cpp: Dafny verified fewer items than the model has methods: 0 for 1.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// Hex literals, exists, forall with two bound names, and true and false prove, decisions 0082 and 0084.
#[test]
fn hex_literals_exists_and_several_bound_names_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-quant.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A hex literal too large for uint64_t is refused, and a shift in a contract has no rule, decisions 0082 and 0088.
#[test]
fn a_hex_literal_too_large_and_a_shift_in_a_contract_are_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-quant-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-quant-refuse.cpp:4: a number above 18446744073709551615: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:9: the contract line has a form the translator cannot read.",
        "model-quant-refuse.cpp:15: an octal number: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:20: a number with the suffix e3: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:25: a number with no digits after 0x: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 5, "{text}");
}

/// An error inside a function of the companion file prints in the words of Dafny, not as a return of a method, decision 0084.
#[test]
fn an_error_in_the_companion_file_prints_in_the_words_of_dafny() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-wording.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-wording.spec.dfy:1: Dafny says: a postcondition could not be proved on this return path.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("may not hold on this return"), "{text}");
}

/// A literal that is too large is an unknown token, never a token the grammar knows. Read as `::`, it would turn
/// `forall j 99999999999999999999 j > j` into `forall j :: j > j`, a requires line that is false. From the review of decision 0082.
#[test]
fn a_literal_that_is_too_large_never_stands_for_another_token() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-quant-junk.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-quant-junk.cpp:4: a number above 18446744073709551615: the translator has no rule for it yet.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// Slices in a contract prove: examples/recursion with Count(v[i..], x), and the size, an element and empty of a part, decision 0085.
#[test]
fn slices_in_a_contract_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-slice.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A slice that may start past the end is named at its contract line, decision 0085.
#[test]
fn prove_names_a_slice_that_may_start_past_the_end() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-slice-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-slice-wrong.cpp:6: the offset may be past the end.", "model-slice-wrong.cpp:8: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// Division and remainder truncate as in C++, in code and in contracts, signed and unsigned, decision 0088.
#[test]
fn division_truncates_as_in_cpp() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-div.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A divisor that may be zero, a quotient that may not fit, also for %, and a contract that expects Dafny's own division, are
/// each named at their lines, decision 0088.
#[test]
fn prove_names_a_division_that_may_fail() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-div-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-div-wrong.cpp:5: the divisor may be zero.",
        "model-div-wrong.cpp:5: the value may not fit int32_t.",
        "model-div-wrong.cpp:10: the value may not fit int32_t.",
        "model-div-wrong.cpp:16: the ensures line may not hold on this return.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 4, "{text}");
}

/// const member functions prove, with the object as a parameter this by value, bare field names in their contracts, a call of a
/// member function inside another and from a free function, and a private field, decision 0089 steps 1 and 2.
#[test]
fn const_member_functions_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-method.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A member function with a ref-qualifier, a static member function, and a contract name that is no parameter and no field, are each
/// refused at their lines, and the rest of the struct still translates, decision 0089.
#[test]
fn member_functions_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-method-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-method-refuse.cpp:7: CXXMethodDecl: the translator has no rule for it yet.",
        "model-method-refuse.cpp:12: CXXMethodDecl: the translator has no rule for it yet.",
        "model-method-refuse.cpp:16: m_ in the contract is no parameter.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 3, "{text}");
}

/// A pure const member function is also a Dafny function. A contract calls valid() inside its struct and c.valid() and c.next()
/// outside it, and a caller of the method knows the value of the function, decision 0090.
#[test]
fn pure_member_functions_are_functions_that_contracts_call() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-pure.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A contract that calls a member function that is not pure, or a name that is no member function, is refused at its line,
/// decision 0090. So is one that calls a member whose own contract is refused, decision 0095.
#[test]
fn a_contract_that_calls_a_member_function_that_is_not_pure_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-pure-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-pure-refuse.cpp:13: copy is no pure function. A contract calls a function with one return and no write.",
        "model-pure-refuse.cpp:18: three is no pure function. A contract calls a function with one return and no write.",
        "model-pure-refuse.cpp:26: nosuch in the contract is no parameter.",
        "model-pure-refuse.cpp:32: refused is no pure function. A contract calls a function with one return and no write.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 4, "{text}");
}

/// An integer argument of a member function in a contract passes as the type of its parameter, from a parameter and from result,
/// decision 0095.
#[test]
fn the_arguments_of_a_member_function_in_a_contract_pass_as_its_parameter_types() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-pure-args.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A contract that calls a member function outside its requires lines is named at the contract line, with the requires line that
/// may not hold, decision 0095.
#[test]
fn prove_names_a_contract_call_outside_the_requires_of_a_member_function() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-pure-args-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let head = "model-pure-args-wrong.cpp:14: a requires line of the member function may not hold here.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(head)), "{head}: {text}");
    assert!(under(&text, head).iter().any(|l| l.ends_with("model-pure-args-wrong.cpp:7: requires n_ < 1000")), "{text}");
}

/// A constructor with only a member init list proves its contract, which names fields and valid() of the value it builds, and a
/// caller that builds a value, in a local and in a return, knows it, decision 0094.
#[test]
fn a_constructor_gives_the_value_it_builds() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-ctor.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A constructor whose body writes a field, one that leaves a field out, a delegating constructor, and one whose init list reads a
/// field are refused at their lines, decisions 0094 and 0179.
#[test]
fn constructors_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-ctor-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let field = "model-ctor-refuse.cpp:9: a field in the body of a constructor: the translator has no rule for it yet.";
    assert!(refusals.iter().any(|l| l.ends_with(field)), "{field}: {text}");
    for line in [12, 14, 22] {
        let want = format!("model-ctor-refuse.cpp:{line}: CXXConstructorDecl: the translator has no rule for it yet.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 4, "{text}");
}

/// A member function that writes its object proves: a field write, compound assignment, a setter that also gives a value, old() in
/// an ensures line, calls on a local that write it back, compound assignment of a local, and a void free function, decision 0096.
#[test]
fn member_functions_that_write_their_object_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-mut.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A field write that may overflow, and an ensures line that does not hold when a void function ends, are named at their lines.
/// The end of a void function is named at the line of the function, decision 0096.
#[test]
fn prove_names_a_write_that_may_overflow_and_an_ensures_line_of_a_void_function() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-mut-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-mut-wrong.cpp:8: the value may not fit int32_t.", "model-mut-wrong.cpp:12: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A call that writes a parameter, a call that writes a field of a local, old() outside the ensures lines of a function that writes
/// its object, a return of a void call, a call alone whose value is dropped, and a write to an optional field, are refused at their
/// lines, decisions 0096 and 0097.
#[test]
fn writes_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-mut-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-mut-refuse.cpp:17: c is a parameter. The translator writes only a local or a reference parameter.",
        "model-mut-refuse.cpp:23: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
        "model-mut-refuse.cpp:27: the contract line has a form the translator cannot read.",
        "model-mut-refuse.cpp:37: ReturnStmt: the translator has no rule for it yet.",
        "model-mut-refuse.cpp:45: a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.",
        "model-mut-refuse.cpp:53: CXXOperatorCallExpr: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
}

/// The conditional operator in code and in contracts, and a struct with an operator() called in code and in a contract, prove,
/// decision 0098.
#[test]
fn conditionals_and_functors_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-cond.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An ensures line that a conditional does not meet, and a branch that may overflow, are named at their lines, decision 0098.
#[test]
fn prove_names_a_conditional_that_does_not_meet_its_contract() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-cond-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-cond-wrong.cpp:6: the ensures line may not hold on this return.", "model-cond-wrong.cpp:10: the value may not fit int32_t."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A contract that calls a functor whose operator() is not pure, and a call of a name that a quantifier binds, are refused at
/// their lines, decisions 0098 and 0100. A call in a branch of a conditional in a return has a model, decision 0177.
#[test]
fn conditionals_and_functors_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-cond-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-cond-refuse.cpp:11: operator() is no pure function. A contract calls a function with one return and no write.",
        "model-cond-refuse.cpp:24: the contract line has a form the translator cannot read.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// Assert lines, apply lines that call lemmas of the companion file, and a loop contract that names a field of the object in a
/// member function that writes it, prove, decision 0099.
#[test]
fn assert_and_apply_lines_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-assert.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An assert line that may not hold, and an apply line whose lemma has a requires line that may not hold, are named at their
/// lines, decision 0099.
#[test]
fn prove_names_an_assert_line_and_an_apply_line_that_may_not_hold() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-assert-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-assert-wrong.cpp:4: the assert line may not hold.", "model-assert-wrong.cpp:9: a requires line of the callee may not hold."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// An assert line that names result, an apply line of a name that is no lemma of the companion file, an assert line below the
/// last statement of its block (also where `} else if` follows), and a name that is not yet in scope, are refused at their
/// lines, decisions 0099 and 0101.
#[test]
fn assert_and_apply_lines_with_no_rule_are_refused_at_their_lines() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-assert-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-assert-refuse.cpp:5: the contract line has a form the translator cannot read.",
        "model-assert-refuse.cpp:10: Missing is no lemma of the companion file.",
        "model-assert-refuse.cpp:17: an assert or apply line needs a statement below it in its block.",
        "model-assert-refuse.cpp:21: Twice is no lemma of the companion file.",
        "model-assert-refuse.cpp:29: an assert or apply line needs a statement below it in its block.",
        "model-assert-refuse.cpp:37: y in the assert line is no variable.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
}

/// A lemma with no body in the companion file is an axiom, so prove refuses the file and never says proved, decision 0099.
#[test]
fn prove_refuses_a_lemma_with_no_body_in_the_companion_file() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-lemma.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-lemma.spec.dfy:2: a lemma with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A forall statement with no body in a lemma of the companion file is an axiom, so prove refuses it at its line and never says
/// proved, decision 0101.
#[test]
fn prove_refuses_a_forall_statement_with_no_body_in_the_companion_file() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-spec-forall.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-forall.spec.dfy:11: a forall statement with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A trusted function is a method with its contract and no body. Its callers prove from the contract, and prove names each
/// trusted function with its reason before the verdict, decision 0102.
#[test]
fn trusted_functions_are_contracts_that_prove_names() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-trusted.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let trusted: Vec<&str> = text.lines().filter(|l| l.starts_with("Trusted: ")).collect();
    for want in [
        "model-trusted.cpp:7: read_status: reads a hardware status register",
        "model-trusted.cpp:18: increment: a body that the translator has no rule for",
    ] {
        assert!(trusted.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(trusted.len(), 2, "{text}");
    // Only the attribute {:axiom} tells Dafny that a method with no body is meant to have none, decision 0102.
    let dir = tempfile::tempdir().unwrap();
    let (_, out) = model("model-trusted.cpp", dir.path());
    let dfy = std::fs::read_to_string(&out).unwrap();
    assert!(dfy.contains("method {:axiom} c_read_status("), "{dfy}");
    assert!(dfy.contains("method {:axiom} c_increment("), "{dfy}");
    assert!(!dfy.contains("method {:axiom} c_headroom("), "{dfy}");
}

/// A caller that needs more than the contract of a trusted function, or that misses its requires line, is not proved. The
/// Trusted: lines come first, before each refusal and each failure, decisions 0102 and 0103.
#[test]
fn prove_names_a_caller_that_needs_more_than_a_trusted_contract() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-trusted-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-trusted-wrong.cpp:12: the ensures line may not hold on this return.", "model-trusted-wrong.cpp:21: a requires line of the callee may not hold."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
    let lines: Vec<&str> = text.lines().collect();
    let trusted: Vec<usize> = (0..lines.len()).filter(|&i| lines[i].starts_with("Trusted: ")).collect();
    let first_fault = (0..lines.len()).find(|&i| lines[i].starts_with("Not provable: ") || lines[i].starts_with("Not proved: ")).unwrap();
    assert_eq!(trusted.len(), 2, "{text}");
    assert!(trusted.iter().all(|&i| i < first_fault), "{text}");
    assert!(lines.iter().any(|l| l.ends_with("model-trusted-wrong.cpp:7: read_status: reads a hardware status register")), "{text}");
    assert!(lines.iter().any(|l| l.ends_with("model-trusted-wrong.cpp:26: BinaryOperator <<: the translator has no rule for it yet.")), "{text}");
}

/// The //@ lines in the body of a trusted definition belong to it and are not read, and the Trusted: line names the marked
/// declaration, decision 0103.
#[test]
fn a_trusted_definition_keeps_the_lines_of_its_body_and_names_its_marked_declaration() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-trusted-body.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let trusted: Vec<&str> = text.lines().filter(|l| l.starts_with("Trusted: ")).collect();
    assert_eq!(trusted.len(), 1, "{text}");
    assert!(trusted[0].ends_with("model-trusted-body.cpp:9: count: counts with a loop"), "{text}");
}

/// A function with no body and no marker has no method, so a call of it is refused at its line, decision 0102.
#[test]
fn a_call_of_a_function_with_no_body_and_no_marker_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-trusted-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let want = "model-trusted-refuse.cpp:8: a call to read_status, which has no model in view.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 1, "{text}");
}

/// A call inside an expression runs before its statement, so a nested call, a call in an operand, a call in a condition, in an
/// else-if condition, in the start and the step of a for loop, and a constructor call prove, decisions 0104 and 0105.
#[test]
fn calls_inside_expressions_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-lift.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A call before its statement keeps the requires lines of its callee, a constructor too, and its value is the value of the
/// callee, decisions 0104 and 0105.
#[test]
fn prove_names_a_call_inside_an_expression_that_does_not_meet_a_contract() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-lift-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-lift-wrong.cpp:10: a requires line of the callee may not hold.",
        "model-lift-wrong.cpp:16: the ensures line may not hold on this return.",
        "model-lift-wrong.cpp:28: a requires line of the callee may not hold.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 3, "{text}");
}

/// A call in a while or for condition is refused at its line: C++ runs it again at each turn, decisions 0104 and 0105. A call on
/// the right of && or || or in a branch of ?: in a return has a model, decision 0177.
#[test]
fn a_call_that_cpp_may_not_run_once_is_refused_at_its_line() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-lift-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let place = "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.";
    for line in [18, 30] {
        let want = format!("model-lift-refuse.cpp:{line}: {place}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

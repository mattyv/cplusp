use super::*;

/// A double that only compares proves as a real, and a clamp that misses part of its range fails at its return, decision 0150.
/// Two functions pin a literal of code to a literal of the contract with another spelling of the same value.
#[test]
fn a_double_that_only_compares_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-double.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-double-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["10: the ensures line may not hold on this return."], "{text}");
}

/// A double operation that rounds, a double parameter with no isfinite, and a trusted double result with no isfinite are refused
/// with their sentences, and a caller of that trusted function is refused too, decision 0150.
#[test]
fn a_double_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-double-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        refusals,
        [
            "11: x is a double. A requires line needs std::isfinite(x).",
            "17: a trusted function that gives a double needs std::isfinite(result) in an ensures line.",
            // `++` on a double stays refused, decision 0154.
            "22: a double operation rounds, and the translator has no rule for it yet.",
            // A caller of the refused trusted function has no model of it.
            "27: a call to reading, which has no model in view.",
        ],
        "{text}"
    );
}

/// The example double_only proves: a trusted reading, and a clamp by comparisons only, decision 0150.
#[test]
fn the_double_only_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/double_only/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each double operation is one rounding of the model, and prove names the axiom once, before its verdict. A product with no
/// bound, an equality that the rounding breaks and a divisor that may be zero fail with their sentences, decision 0154.
#[test]
fn a_double_operation_is_one_rounding() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-double-ops.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.last(), Some(&"ok: proved"), "{text}");
    assert_eq!(lines.iter().filter(|l| **l == AXIOM).count(), 1, "{text}");
    assert_eq!(lines[lines.len() - 2], AXIOM, "{text}");
    let o = prove("model-double-ops-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().filter(|l| *l == AXIOM).count(), 1, "{text}");
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        [
            "8: the result of the operation may exceed DBL_MAX.",
            "15: the ensures line may not hold on this return.",
            "21: the divisor may be zero.",
            // A contract that divides by a divisor that may be zero, decision 0154.
            "25: the divisor may be zero.",
        ],
        "{text}"
    );
    // A model with no rounding names no axiom, even with a bar in its contract.
    let o = prove("model-double.cpp", &[], &dafny);
    assert_eq!(stdout(&o).lines().last(), Some("ok: proved"), "{}", stdout(&o));
    assert!(!stdout(&o).contains("Axiom:"), "{}", stdout(&o));
}

/// A named double constant, an exact double with no short decimal, and a whole number next to a real prove, and a wrong contract
/// with them fails at its return, decision 0158.
#[test]
fn a_named_double_and_an_exact_double_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-double-const.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-double-const-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["8: the ensures line may not hold on this return.", "13: the ensures line may not hold on this return."], "{text}");
}

/// A constant of a namespace hides the double constant of the file, and a double that the model cannot write exactly is refused in
/// code and in a contract, decision 0158.
#[test]
fn a_double_that_the_model_cannot_write_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-double-const-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let exact = "a double literal that the model cannot write exactly: the translator has no rule for it yet.";
    assert_eq!(
        refusals,
        [
            "11: T in the contract is no parameter.".to_string(),
            format!("19: {exact}"),
            "24: a double constant that the model cannot write exactly: the translator has no rule for it yet.".to_string(),
            "27: TINY in the contract is no parameter.".to_string(),
            "37: U in the contract is no parameter.".to_string(),
        ],
        "{text}"
    );
}

/// A name that C++ finds from the function with the name of a contract word is refused where a contract reads the word, because
/// the word hides the name of C++, decision 0158. A name of that spelling is no clash where no contract reads the word.
#[test]
fn a_name_of_cpp_with_the_name_of_a_contract_word_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let word = |w: &str| format!("{w} in the contract is a contract word, and a C++ name too. Rename the C++ name.");
    let cases: [(&str, &[(u32, &str)]); 3] = [
        ("model-word-constant.cpp", &[(8, "eps"), (13, "eta")]),
        // A parameter, a field, and a parameter of the declaration that the definition names in another way.
        ("model-word-name.cpp", &[(4, "eps"), (11, "eta"), (24, "eps")]),
        // A static member, a member defined out of line, a namespace constant, a global variable, a function that finds none, and a
        // friend that a class defines.
        ("model-word-scope.cpp", &[(10, "eps"), (17, "eta"), (25, "eps"), (31, "eta"), (44, "eta")]),
    ];
    for (fixture, wants) in cases {
        let dir = tempfile::tempdir().unwrap();
        let (o, _) = model(fixture, dir.path());
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{fixture}: stdout: {text} stderr: {}", stderr(&o));
        let refusals: Vec<&str> =
            text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
        let wants: Vec<String> = wants.iter().map(|(line, w)| format!("{line}: {}", word(w))).collect();
        assert_eq!(refusals, wants, "{fixture}: {text}");
    }
}

/// An integer converts to a double with no rounding up to 2^53, and prove names the axiom of the conversion. A conversion with no
/// bound and an absolute value that the body does not give fail at their lines, decision 0159.
#[test]
fn an_integer_converts_to_a_double_exactly() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let exact = "Axiom: Double.dfy: RoundExactInt: an integer up to 2^53 in magnitude is a double.";
    let o = prove("model-double-convert.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.last(), Some(&"ok: proved"), "{text}");
    assert_eq!(lines.iter().filter(|l| **l == exact).count(), 1, "{text}");
    // `shift` also rounds once.
    assert_eq!(lines.iter().filter(|l| **l == AXIOM).count(), 1, "{text}");
    let o = prove("model-double-convert-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["6: the integer may be too large for an exact double.", "11: the ensures line may not hold on this return."],
        "{text}"
    );
    // A conversion alone names its own axiom and not the one of the operations.
    assert!(text.contains(exact) && !text.contains(AXIOM), "{text}");
}

/// A local vector is a copy: a write to the copy leaves the vector of the caller as it was, and a write to the vector after the copy
/// leaves the copy as it was, decision 0160. A contract that reads the copy as the vector, or the vector as a view, fails.
#[test]
fn prove_treats_a_local_vector_as_a_copy() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-local.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-local-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["10: the ensures line may not hold on this return.", "20: the ensures line may not hold on this return."],
        "{text}"
    );
}

/// A local vector from a list of values has no rule yet, decision 0160. A local vector with no initial value is the empty sequence,
/// and a call that passes one by reference writes it back, decision 0170.
#[test]
fn a_local_vector_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-vec-local-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let copy = "a local vector has a rule only as a copy of a vector in scope.";
    assert_eq!(refusals, [format!("15: {copy}")], "{text}");
}

/// std::sort of a vector of integers is StdSort: the order, the length and the multiset hold after the call, and prove names the
/// trusted contract once, decision 0161. A claim of the other order, or of the old first element, fails at its return.
#[test]
fn std_sort_of_a_vector_of_integers_is_std_sort() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-sort.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.last(), Some(&"ok: proved"), "{text}");
    assert_eq!(lines.iter().filter(|l| **l == SORT_AXIOM).count(), 1, "{text}");
    assert!(!text.contains("Axiom: Double.dfy"), "{text}");
    let o = prove("model-sort-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["11: the ensures line may not hold on this return.", "19: the ensures line may not hold on this return."],
        "{text}"
    );
    // A model with no sort names no axiom of the sort.
    let o = prove("model-vec-local.cpp", &[], &dafny);
    assert!(!stdout(&o).contains("Algorithm.dfy"), "{}", stdout(&o));
}

/// A std::sort of a part of a range, with a comparator that is no lambda of the element type and one return, or over two vectors is
/// refused with one sentence that names std::sort, decisions 0161 and 0162.
#[test]
fn std_sort_of_another_form_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-sort-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let other = "std::sort of another form: the translator has no rule for it yet.";
    // A named function as a comparator, a lambda of another type, a lambda of two statements, a lambda of two types and a lambda
    // with a parameter that it can write, decision 0162.
    let lines = [13, 19, 26, 32, 38, 47, 53];
    assert_eq!(refusals, lines.map(|l| format!("{l}: {other}")), "{text}");
}

/// std::sort with a comparator lambda is StdSort with the lambda: an order down and a capture by copy prove,
/// decision 0162. A comparator that is not a strict weak order fails at the call with its own sentence.
#[test]
fn std_sort_with_a_comparator_lambda_is_std_sort_with_the_lambda() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-sort-by.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.last(), Some(&"ok: proved"), "{text}");
    assert_eq!(lines.iter().filter(|l| **l == SORT_AXIOM).count(), 1, "{text}");
    let o = prove("model-sort-by-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let order = "the comparator may not be a strict weak order.";
    assert_eq!(failed, [format!("9: {order}"), format!("16: {order}")], "{text}");
}

/// A vector of a struct by reference, as a local and as a result, a sort of it by a field, a local from a call that gives a vector,
/// and a vector of integers as a result prove, decision 0163. A wrong size of a result fails at its return.
#[test]
fn a_vector_of_a_struct_and_a_vector_as_a_result_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-struct.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-struct-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["10: the ensures line may not hold on this return."], "{text}");
}

/// A vector that may outgrow its bound, a lemma of the companion file whose proof fails, and a comparator that breaks two clauses
/// of a strict weak order each have a plain sentence, and a failure prints one line, decision 0164. The ensures failure of the lemma
/// names its ensures line.
#[test]
fn a_vector_too_long_and_a_failed_lemma_have_plain_sentences() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let failed = |name: &str| {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.to_string()).collect::<Vec<String>>()
    };
    let at = |lines: Vec<String>| -> Vec<String> { lines.iter().map(|l| l.rsplit_once(".cpp:").unwrap().1.to_string()).collect() };
    assert_eq!(at(failed("model-vec-result-bound-wrong.cpp")), ["15: the vector may be too long.", "22: the vector may be too long."]);
    assert_eq!(at(failed("model-sort-by-once.cpp")), ["13: the comparator may not be a strict weak order."]);
    // The lemma failures name the companion file, and each says what failed in the words of the model.
    let lemmas = failed("model-companion-fail.cpp");
    assert!(lemmas.iter().all(|l| l.contains("model-companion-fail.spec.dfy:")), "{lemmas:?}");
    let said: Vec<&str> = lemmas.iter().map(|l| l.rsplit_once(": ").unwrap().1).collect();
    assert_eq!(said, ["the ensures line may not hold on this return.", "the assert line may not hold."], "{lemmas:?}");
    let o = prove("model-companion-fail.cpp", &[], &dafny);
    let named = blocks(&stdout(&o)).into_iter().any(|(h, under)| {
        h.ends_with("the ensures line may not hold on this return.")
            && under.iter().any(|u| u.ends_with("model-companion-fail.spec.dfy:2: ensures x > 0"))
    });
    assert!(named, "{}", stdout(&o));
}

/// Two clauses of a lemma of the companion file that fail, as ensures lines or as requires lines at an apply, give two lines, each
/// with the line of the companion file that it breaks, decision 0164. Two reads on one line that may each be out of range give two
/// lines.
#[test]
fn two_failures_at_one_place_stay_two_lines() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-companion-two.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let found = blocks(&text);
    let broken = |head: &str, clause: &str| {
        found
            .iter()
            .filter(|(h, under)| h.ends_with(head) && under.iter().any(|u| u.starts_with("  The contract line: ") && u.ends_with(clause)))
            .count()
    };
    let ensures = "the ensures line may not hold on this return.";
    assert_eq!(broken(ensures, "model-companion-two.spec.dfy:2: ensures x > 0"), 1, "{text}");
    assert_eq!(broken(ensures, "model-companion-two.spec.dfy:3: ensures x < 0"), 1, "{text}");
    let callee = "model-companion-two.cpp:7: a requires line of the callee may not hold.";
    assert_eq!(broken(callee, "model-companion-two.spec.dfy:8: requires x > 0"), 1, "{text}");
    assert_eq!(broken(callee, "model-companion-two.spec.dfy:9: requires x < 0"), 1, "{text}");
    assert_eq!(found.len(), 4, "{text}");
    let o = prove("model-two-index.cpp", &[], &dafny);
    let text = stdout(&o);
    let index = text
        .lines()
        .filter(|l| l.starts_with("Not proved: ") && l.ends_with("model-two-index.cpp:9: the index may be out of range."))
        .count();
    assert_eq!(index, 2, "{text}");
}

/// The examples double and double_expression prove: a tolerance that is a named double, and one error term for each rounding,
/// decision 0158. The example fixed_point converts an integer to a double, decision 0159. The example algorithms sorts a copy,
/// decision 0161, and sort_with_comparator sorts a copy of a vector of a struct by a field and gives it back, decision 0163.
#[test]
fn the_double_examples_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for example in ["double", "double_expression", "fixed_point", "algorithms", "sort_with_comparator"] {
        let o = prove(&format!("../../../../examples/{example}/example.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{example}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{example}: {text}");
    }
}

/// Each refusal names its own cause: a contract line with no rule, a conversion, a long decimal, and a parameter with no name,
/// decision 0155.
#[test]
fn each_refusal_names_its_own_cause() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-sentences-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 5, "{text}");
    assert_eq!(refusals[0], "5: isnan is no function of the companion file.", "{text}");
    assert!(
        refusals[1].starts_with("12: ")
            && refusals[1].contains("FloatingToIntegral")
            && refusals[1].ends_with(": the translator has no rule for it yet."),
        "{text}"
    );
    assert_eq!(refusals[2], "15: a decimal with more than 19 digits after the point: the translator has no rule for it yet.", "{text}");
    assert_eq!(refusals[3], "20: a reference parameter has no name. Give it a name and put it on the modifies line.", "{text}");
    assert_eq!(refusals[4], "23: a double parameter has no name. Give it a name and say std::isfinite of it in a requires line.", "{text}");
}

/// A check that Dafny reports twice, the condition of a loop at its start and after a turn, is printed once, decision 0155.
#[test]
fn a_failure_is_printed_once() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-dedup.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["10: the value may not fit uint64_t."], "{text}");
}

/// Two failures at one place of the model, each with its own contract line, are both printed, decision 0155.
#[test]
fn two_failures_at_one_place_are_both_printed() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-dedup-two.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["7: the ensures line may not hold on this return.", "7: the ensures line may not hold on this return."], "{text}");
    let contract: Vec<&str> = text.lines().filter(|l| l.trim_start().starts_with("The contract line: ")).collect();
    assert_eq!(contract.len(), 2, "{text}");
    assert!(contract[0].contains("model-dedup-two.cpp:4:") && contract[1].contains("model-dedup-two.cpp:5:"), "{text}");
}

/// When a team bans variable_index, a variable index into a vector or a span, and at() with a variable index, are findings, as one
/// into an array is. A constant index stays allowed, decision 0156.
#[test]
fn a_ban_of_variable_index_covers_vectors_spans_and_at() {
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-tighten.yaml");
    let f = fixture("variable-index-ban.cpp");
    let o = gated(&["--policy", team.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let lines: BTreeSet<&str> = text
        .lines()
        .filter(|l| l.contains("`operator[]` with a variable index"))
        .filter_map(|l| l.split("variable-index-ban.cpp:").nth(1))
        .filter_map(|r| r.split(':').next())
        .collect();
    // An explicit `operator[]` call and a C array by reference too, which the upstream check misses.
    assert_eq!(lines, BTreeSet::from(["8", "12", "16", "24", "28"]), "{text}");
}

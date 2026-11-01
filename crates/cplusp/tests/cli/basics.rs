use super::*;

/// The first slice, decision 0057: the translator turns clamp into a Dafny method, and Dafny proves it as it proves the hand-written
/// model of examples/saturating_add.
#[test]
fn the_model_of_clamp_verifies_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-clamp.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(text.contains("method c_clamp("), "{text}");
    let v = Command::new(dafny).args(["verify"]).arg(&out).output().unwrap();
    let said = format!("{}{}", String::from_utf8_lossy(&v.stdout), String::from_utf8_lossy(&v.stderr));
    assert!(v.status.success() && said.contains(" 0 errors"), "{said}\n{text}");
}

/// The contract reaches the model: a wrong ensures line makes Dafny fail.
#[test]
fn a_wrong_contract_fails_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-clamp-wrong.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    let v = Command::new(dafny).args(["verify"]).arg(&out).output().unwrap();
    let said = format!("{}{}", String::from_utf8_lossy(&v.stdout), String::from_utf8_lossy(&v.stderr));
    assert!(!v.status.success() && said.contains("postcondition"), "{said}\n{text}");
}

/// A construct with no rule and a contract name that is no parameter are refused, each at its line, with the gate's prefix. The
/// functions that the translator can model are still in the model.
#[test]
fn the_translator_refuses_what_it_has_no_rule_for() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 2, "{text}");
    assert!(
        refusals.iter().any(|l| l.ends_with("model-refuse.cpp:9: BinaryOperator <<: the translator has no rule for it yet.")),
        "{text}"
    );
    assert!(refusals.iter().any(|l| l.ends_with("model-refuse.cpp:12: y in the contract is no parameter.")), "{text}");
    let model = std::fs::read_to_string(&out).unwrap();
    assert!(full(&model, "one"), "{model}");
    // Decision 0058: a refused function keeps its signature, with no contract and no body.
    assert!(bare(&model, "call_one") && bare(&model, "named"), "{model}");
}

/// Each function in view is modelled or refused, and each contract line belongs to a function or is refused, decision 0057. A
/// template is refused, not skipped. A function in a project header is in view. A contract line apart from its function, behind a
/// comment, or that ends in a backslash is refused. A deleted function runs nothing, so it has no model and no refusal.
#[test]
fn every_function_and_contract_line_in_view_is_modelled_or_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-coverage.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for expected in [
        "model-coverage.cpp:7: a function template with no instance: the translator has no rule for it yet.",
        "model-coverage.cpp:12: a function template with no instance: the translator has no rule for it yet.",
        "model-coverage.cpp:16: a contract line that belongs to no function.",
        "model-coverage.cpp:22: a contract line that belongs to no function.",
        "model-coverage.cpp:28: a contract line that ends in a backslash.",
        "model-coverage.cpp:34: '=' in a contract: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(expected)), "{expected}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
    let model = std::fs::read_to_string(&out).unwrap();
    for name in ["in_header", "apart", "noted"] {
        assert!(
            model.contains(&format!("method {name}(")) || model.lines().any(|l| l.starts_with("method ") && l.contains(name)),
            "{name}: {model}"
        );
    }
    for name in ["tmpl", "abbreviated", "gone"] {
        assert!(!model.lines().any(|l| l.starts_with("method ") && l.contains(name)), "{name}: {model}");
    }
    // Decision 0058: a refused contract keeps the signature, with no contract and no body.
    for name in ["continued", "arrow"] {
        assert!(bare(&model, name), "{name}: {model}");
    }
}

/// A name that Dafny reserves, a parameter with no name, and a tab after the word of a contract line still give a model that Dafny
/// proves, decision 0057. A parameter with no name never shares a Dafny name with one the author named, decision 0059. A parameter
/// with the name of a function never shares a Dafny name with the method, decision 0060.
#[test]
fn reserved_names_and_unnamed_parameters_still_give_a_model_dafny_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-names.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert_eq!(text.lines().filter(|l| l.starts_with("method ")).count(), 5, "{text}");
    let v = Command::new(dafny).args(["verify"]).arg(&out).output().unwrap();
    let said = format!("{}{}", String::from_utf8_lossy(&v.stdout), String::from_utf8_lossy(&v.stderr));
    assert!(v.status.success() && said.contains(" 0 errors"), "{said}\n{text}");
}

/// A file that does not compile cannot be modelled. It is exit 2, with the gate's message.
#[test]
fn a_file_that_does_not_compile_has_no_model() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-broken.cpp", dir.path());
    let err = stderr(&o);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {err}", stdout(&o));
    assert!(err.lines().any(|l| l.starts_with("does not compile: ") && l.contains("model-broken.cpp:4:")), "{err}");
}

/// The second slice, decision 0058: the example of saturating_add has a local, casts and a call, and each of its three functions
/// has a model that Dafny proves.
#[test]
fn the_model_of_saturating_add_and_successor_verifies_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/saturating_add/example.cpp");
    let (o, out) = model_of(&example, dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    for name in ["saturating_add", "clamp", "successor"] {
        assert!(full(&text, name), "{name}: {text}");
    }
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// Each call, local and cast that the second slice has no rule for is refused at its line, decisions 0058 and 0104. A refused function keeps a
/// method with no contract and no body, so its callers still have a model, and the model still resolves in Dafny.
#[test]
fn calls_locals_and_casts_with_no_rule_are_refused_at_their_lines() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-calls.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, expected) in [
        (20, "a call to declared, which has no model in view."),
        (24, "CXXMethodDecl: the translator has no rule for it yet."),
        (28, "a call to T::one, which has no model in view."),
        (34, "y is declared twice in the function."),
        (42, "x is declared twice in the function."),
        (49, "a conversion between bool and a number."),
        (54, "DeclStmt: the translator has no rule for it yet."),
        (59, "DeclStmt: the translator has no rule for it yet."),
        (64, "'=' in a contract: the translator has no rule for it yet."),
        (77, "BinaryOperator <<: the translator has no rule for it yet."),
        (90, "CXXDefaultArgExpr: the translator has no rule for it yet."),
    ] {
        let want = format!("model-calls.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 11, "{text}");
    let model = std::fs::read_to_string(&out).unwrap();
    // Decision 0061 gives `y = 2;` in `assigns` a rule, and decision 0104 a call inside an expression in `inside` and `nested`.
    for name in ["id", "calls_bad", "calls_refused", "add", "assigns", "inside", "nested"] {
        assert!(full(&model, name), "{name}: {model}");
    }
    for name in
        ["to_declared", "to_member", "twice", "shadow", "from_bool", "no_start", "two_names", "bad_contract", "refused_body", "defaulted"]
    {
        assert!(bare(&model, name), "{name}: {model}");
    }
    assert!(method_lines(&model, "declared").is_none() && method_lines(&model, "one").is_none(), "{model}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{model}");
}

/// Overloads and one name in two namespaces are different functions, each with its own method and Dafny name, decision 0058. This
/// closes the finding of the review of slice 1 that two methods had one name and Dafny refused the file.
#[test]
fn overloads_and_namespaces_each_have_their_own_method() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-overloads.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    let headers: Vec<&str> = text.lines().filter(|l| l.starts_with("method ")).map(|l| &l[..l.find('(').unwrap()]).collect();
    let distinct: std::collections::BTreeSet<&str> = headers.iter().copied().collect();
    assert_eq!((headers.len(), distinct.len()), (7, 7), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// Two overloads from one expansion of a macro are two functions with two methods, decision 0058. A key from the place of the
/// expansion alone would give them one.
#[test]
fn overloads_from_one_macro_each_have_their_own_method() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-macro.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    let headers: Vec<&str> = text.lines().filter(|l| l.starts_with("method ")).map(|l| &l[..l.find('(').unwrap()]).collect();
    let distinct: std::collections::BTreeSet<&str> = headers.iter().copied().collect();
    assert_eq!((headers.len(), distinct.len()), (4, 4), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// A literal keeps its type, decision 0060, and the model never wraps, decision 0061. C++ wraps `-1u` and `0u - 1u`, and a model that
/// dropped the type proved `-1u < 1u` true. Now each wrap fails in Dafny.
#[test]
fn an_unsigned_wrap_of_literals_fails_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-unsigned.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "wrong") && full(&text, "wrong_sub"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(!ok && said.contains(" 2 errors"), "{said}\n{text}");
}

/// A contract on a declaration reads that declaration's parameters by place, decision 0060. The definition may name them otherwise.
/// With the same order the model proves. With the names swapped, the C++ breaks its contract and Dafny refuses it.
#[test]
fn a_contract_on_a_declaration_reads_its_parameters_by_place() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-redecl.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "minus"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");

    let (o, out) = model("model-redecl-wrong.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    let (ok, said) = verify(&dafny, &out);
    assert!(!ok && said.contains("postcondition"), "{said}\n{text}");
}

/// The third slice, decision 0061: a for loop, a while loop, writes to locals and an unsigned count, each with its invariant and
/// decreases lines, give methods that Dafny proves.
#[test]
fn loops_with_invariants_verify_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-loops.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    for name in ["triangle", "down", "count"] {
        assert!(full(&text, name), "{name}: {text}");
    }
    assert!(text.lines().filter(|l| l.trim_start().starts_with("invariant ")).count() == 4, "{text}");
    assert!(text.lines().filter(|l| l.trim_start().starts_with("decreases ")).count() == 3, "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// Each loop, write and loop contract that the third slice has no rule for is refused at its line, decision 0061.
#[test]
fn loops_and_writes_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-loops-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let misplaced =
        "a contract line in the wrong place. A requires, an ensures, a modifies or a decreases line goes above a function. An invariant or a decreases line goes above a loop, and an index line above a range-for.";
    for (line, expected) in [
        (5, "x is a parameter. The translator writes only a local or a reference parameter."),
        (11, "BinaryOperator <<=: the translator has no rule for it yet."),
        (18, "BreakStmt: the translator has no rule for it yet."),
        (25, "z in the invariant line is no variable."),
        (32, misplaced),
        (39, misplaced),
        (48, "the contract line has a form the translator cannot read."),
        (56, "ForStmt: the translator has no rule for it yet."),
        (64, "t in the invariant line is no variable."),
        (74, "z in the invariant line is no variable."),
    ] {
        let want = format!("model-loops-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 10, "{text}");
}

/// A `//@` line after code on the same line belongs to no function and no loop, decision 0062. Each is refused, never dropped.
#[test]
fn a_contract_line_after_code_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-trailing.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for line in [4, 9, 13] {
        let want = format!("model-trailing.cpp:{line}: a contract line that belongs to no function.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 3, "{text}");
}

/// A loop on the line of its function's name leaves the function its contract lines, decision 0062.
#[test]
fn a_loop_on_the_line_of_its_function_leaves_the_function_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-oneline.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "w4") && text.contains("  requires ") && text.contains("  ensures "), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// `true` and `false` in code are bool literals, decision 0063, and the model proves what they say.
#[test]
fn bool_literals_verify_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-bool.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "yes") && full(&text, "no"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// A literal holds the full range of uint64_t, in code and in a contract, decision 0063.
#[test]
fn the_largest_uint64_literal_verifies_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-u64.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "top"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// A refusal of a contract line in a header names the header and its line, decision 0063, not the line of that number in the source
/// file.
#[test]
fn a_contract_line_in_a_header_is_refused_at_the_header() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-header-contract.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 1, "{text}");
    assert!(refusals[0].ends_with("model-header-contract.h:3: '=' in a contract: the translator has no rule for it yet."), "{text}");
}

/// The fourth slice, decision 0064: a const vector and a span of const are Dafny sequences, read by size and index, and contracts
/// read them with `forall` and chained comparisons. `find` from examples/control_flow proves.
#[test]
fn read_only_sequences_verify_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-seq.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "find") && full(&text, "all_below"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(ok && said.contains(" 0 errors"), "{said}\n{text}");
}

/// The model reads a sequence only in range, decision 0064. A read with no check that the index fits fails in Dafny.
#[test]
fn a_read_out_of_range_fails_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-seq-wrong.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "first"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(!ok && said.contains("index out of range"), "{said}\n{text}");
}

/// Each sequence with no rule is refused at its line, decision 0064: a mutable view, a vector of bool, a sequence that is no
/// parameter, a member call other than size, an index of a scalar, and a chain of two directions.
#[test]
fn sequences_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-seq-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    // The plugin names a type outside the subset as the compiler prints it.
    for (line, ty) in [(10, "std::span<int32_t>"), (14, "std::vector<bool>")] {
        let at = format!("model-seq-refuse.cpp:{line}: ");
        assert!(
            refusals.iter().any(|l| l.contains(&at) && l.contains(ty) && l.ends_with(": the translator has no rule for it yet.")),
            "{at}{ty}: {text}"
        );
    }
    for (line, expected) in [
        // A vector by reference is in the subset since decision 0145, so line 6 lacks only its modifies line.
        (6, "v is a reference parameter that the modifies line does not name."),
        (19, "a sequence is in the subset only as a parameter."),
        (27, "a sequence is in the subset only as a parameter."),
        (31, "the contract line has a form the translator cannot read."),
        (36, "the contract line has a form the translator cannot read."),
    ] {
        let want = format!("model-seq-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    // `v.at(0)` at line 24 has a rule since decision 0139.
    assert_eq!(refusals.len(), 7, "{text}");
}

/// A sequence stays one value across a call only because the gate refuses a callee that writes the data behind it, decision 0067.
/// The model alone would read the span as constant across `g()`. The gate refuses the write, and the translator refuses `g`.
#[test]
fn a_callee_that_writes_the_data_behind_a_sequence_is_refused_by_the_gate() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("model-seq-global.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l.contains("model-seq-global.cpp:8: ") && l.contains("gv changes")), "{text}");
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-seq-global.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(
        text.lines().any(|l| l.ends_with("model-seq-global.cpp:8: BinaryOperator =: the translator has no rule for it yet.")),
        "{text}"
    );
}

/// A name that `forall` binds is an exact integer, decision 0067, so the file resolves when the body does not use it or a second
/// forall binds the same name.
#[test]
fn a_bound_name_is_an_integer() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-forall.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(text.contains("forall b_j: int :: "), "{text}");
    // The file resolves and proves. Dafny also warns that these quantifiers have no trigger, which is true of this fixture and
    // does not touch soundness, so the exit status is not the claim here.
    let (_, said) = verify(&dafny, &out);
    assert!(said.contains(" 0 errors") && !said.contains("resolution"), "{said}\n{text}");
}

/// The model never wraps, decision 0061. An unsigned value below zero and a sum of literals that overflows each fail in Dafny.
#[test]
fn unsigned_wrap_and_literal_overflow_fail_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-wrap.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "below") && full(&text, "over"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(!ok && said.contains(" 2 errors"), "{said}\n{text}");
}

/// The model does not wrap a narrowing cast, decision 0058. Dafny must prove that the value fits, and with no contract it cannot.
#[test]
fn a_narrowing_cast_that_may_not_fit_fails_in_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-narrow.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(full(&text, "cut"), "{text}");
    let (ok, said) = verify(&dafny, &out);
    assert!(!ok && said.contains("int32"), "{said}\n{text}");
}

/// A file that proves gives `ok: proved` and exit 0, decision 0068.
#[test]
fn prove_says_ok_when_each_method_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-clamp.cpp", &[], &dafny);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stdout(&o).lines().last(), Some("ok: proved"), "{}", stdout(&o));
}

/// A failed ensures is named at the C++ return, with the contract line it comes from and the requires lines it had, decision 0068.
#[test]
fn prove_names_a_failed_ensures_at_its_return_with_its_contract_and_assumptions() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-clamp-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let lines = under(&text, "model-clamp-wrong.cpp:8: the ensures line may not hold on this return.");
    assert!(
        lines
            .iter()
            .any(|l| l.starts_with("  The contract line: ") && l.ends_with("model-clamp-wrong.cpp:5: ensures x < lo ==> result == hi")),
        "{text}"
    );
    assert!(lines.iter().any(|l| l.starts_with("  It assumes: ") && l.ends_with("model-clamp-wrong.cpp:4: requires lo <= hi")), "{text}");
    assert_eq!(text.lines().filter(|l| l.starts_with("Not proved: ")).count(), 1, "{text}");
}

/// A value that may not fit its type and an index that may be out of range are each named at their C++ line, in words a bot reads,
/// decision 0068. The type is the C++ type.
#[test]
fn prove_names_a_value_that_may_not_fit_and_an_index_out_of_range() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-wrap.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-wrap.cpp:6: the value may not fit uint32_t.", "model-wrap.cpp:11: the value may not fit int32_t."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
    let o = prove("model-seq-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(
        text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with("model-seq-wrong.cpp:6: the index may be out of range.")),
        "{text}"
    );
}

/// A loop invariant that fails at the start, one that the loop does not keep, and a requires line of a callee that the caller may
/// not meet are each named at their C++ line, decision 0068.
#[test]
fn prove_names_failed_invariants_and_a_callee_requires() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-prove-loops.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let lines = under(&text, "model-prove-loops.cpp:7: the invariant may not hold when the loop starts.");
    assert!(lines.iter().any(|l| l.starts_with("  It assumes: ") && l.ends_with("model-prove-loops.cpp:4: requires 0 <= n")), "{text}");
    under(&text, "model-prove-loops.cpp:18: the loop may not keep the invariant.");
    let lines = under(&text, "model-prove-loops.cpp:32: a requires line of the callee may not hold.");
    assert!(
        lines.iter().any(|l| l.starts_with("  The contract line: ") && l.ends_with("model-prove-loops.cpp:26: requires x > 0")),
        "{text}"
    );
    assert_eq!(text.lines().filter(|l| l.starts_with("Not proved: ")).count(), 3, "{text}");
}

/// A method that reaches the time limit is unknown, not false, decision 0068. Z3 settles the slow contract at random under load, so
/// the test runs a stand-in for Dafny that prints the line Dafny prints for a time limit.
#[test]
fn prove_says_a_time_limit_is_unknown() {
    if dafny().is_none() || !clang_tidy_available() {
        return;
    }
    let o = prove("model-prove-slow.cpp", &["--time-limit", "1"], &fixture("fake-dafny-timeout.sh"));
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-prove-slow.cpp:5: the prover reached its time limit. The result is unknown.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{text}");
    assert!(!text.contains("may not hold"), "{text}");
}

/// `prove` runs the gate first, decisions 0067 and 0068. A file the gate refuses gets the gate's findings and no proof.
#[test]
fn prove_runs_the_gate_first() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-seq-global.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l.contains("model-seq-global.cpp:8: ") && l.contains("gv changes")), "{text}");
    assert!(!text.contains("Not proved: ") && !text.contains("BinaryOperator ="), "{text}");
}

/// A model that Dafny cannot read, or a run of Dafny with no summary, is no proof, decision 0069. `prove` exits 2 and says the prover
/// failed. It never says ok, and it never names a C++ line for an error of the model.
#[test]
fn prove_stops_when_the_prover_cannot_read_the_model() {
    if dafny().is_none() || !clang_tidy_available() {
        return;
    }
    for stand_in in ["fake-dafny-parse-error.sh", "fake-dafny-silent.sh"] {
        let o = prove("model-clamp.cpp", &[], &fixture(stand_in));
        let (text, err) = (stdout(&o), stderr(&o));
        assert_eq!(o.status.code(), Some(2), "{stand_in}: stdout: {text} stderr: {err}");
        assert!(err.starts_with("dafny failed"), "{stand_in}: {err}");
        assert!(!text.contains("Not proved: ") && !text.contains("ok: proved"), "{stand_in}: {text}");
    }
}

/// A name with a character that Dafny cannot read is refused, decision 0069, so the model always parses.
#[test]
fn a_name_dafny_cannot_read_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-names-bad.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l.ends_with("model-names-bad.cpp:4: a$b: a name with a character Dafny cannot read.")), "{text}");
}

/// `prove` runs the gate under the team's policy, decision 0069. A row the team tightened refuses the file before any proof.
#[test]
fn prove_runs_the_gate_under_the_teams_policy() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-tighten.yaml");
    let o = prove("model-prove-policy.cpp", &["--policy", team.to_str().unwrap()], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l.contains("model-prove-policy.cpp:7: `operator[]` with a variable index")), "{text}");
    assert!(!text.contains("Not proved: ") && !text.contains("ok: proved"), "{text}");
}

/// Each obligation keeps its own line and its own assumptions, decision 0069. The start and the step of a for loop have their own
/// lines. An ensures line assumes the requires lines. A loop keeps an invariant under all the invariants of the loop, and at the
/// start it has only what holds before the loop.
#[test]
fn prove_gives_each_obligation_its_own_line_and_assumptions() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-prove-places.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-prove-places.cpp:8: the value may not fit uint32_t.", "model-prove-places.cpp:10: the value may not fit uint32_t."]
    {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
    let lines = under(&text, "model-prove-places.cpp:18: the index may be out of range.");
    assert!(
        lines.iter().any(|l| l.starts_with("  It assumes: ") && l.ends_with("model-prove-places.cpp:17: requires v[10] == 0")),
        "{text}"
    );
    let lines = under(&text, "model-prove-places.cpp:27: the loop may not keep the invariant.");
    assert!(lines.iter().any(|l| l.ends_with("model-prove-places.cpp:24: requires 0 <= n && n <= 10")), "{text}");
    assert!(lines.iter().any(|l| l.ends_with("model-prove-places.cpp:28: invariant 0 <= j")), "{text}");
    let lines = under(&text, "model-prove-places.cpp:39: the invariant may not hold when the loop starts.");
    assert!(lines.iter().any(|l| l.ends_with("model-prove-places.cpp:36: requires 0 <= n")), "{text}");
    assert!(!lines.iter().any(|l| l.contains("model-prove-places.cpp:40:")), "{text}");
    // The condition of a loop holds under all the invariants of the loop.
    let lines = under(&text, "model-prove-places.cpp:53: the index may be out of range.");
    assert!(lines.iter().any(|l| l.starts_with("  It assumes: ") && l.ends_with("model-prove-places.cpp:51: invariant i <= 10")), "{text}");
}

/// `prove` says ok only when Dafny exits 0 and its summary says 0 errors, decision 0070. A summary with an error that has no line, or
/// one that disagrees with the exit status, is a fault of the tool.
#[test]
fn prove_never_says_ok_when_the_summary_or_the_exit_status_says_otherwise() {
    if dafny().is_none() || !clang_tidy_available() {
        return;
    }
    for stand_in in ["fake-dafny-summary-errors.sh", "fake-dafny-exit-zero-errors.sh"] {
        let o = prove("model-clamp.cpp", &[], &fixture(stand_in));
        let (text, err) = (stdout(&o), stderr(&o));
        assert_eq!(o.status.code(), Some(2), "{stand_in}: stdout: {text} stderr: {err}");
        assert!(err.starts_with("dafny failed"), "{stand_in}: {err}");
        assert!(!text.contains("ok: proved"), "{stand_in}: {text}");
    }
}

/// A span with a fixed extent keeps its length, decision 0070, so a contract on its size and a read at index 0 prove.
#[test]
fn a_span_with_a_fixed_extent_keeps_its_length() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-span-fixed.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A span, a const vector and a span of fixed extent each pass to a span parameter with their value, decision 0070.
#[test]
fn a_sequence_passes_to_a_sequence_parameter() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-span-copy.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A recursion with a decreases line above its function proves, decision 0072.
#[test]
fn a_recursion_with_its_measure_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-recursion.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A recursive call whose measure may not get smaller is named at the call, and a decreases line above a function that names
/// `result` is refused, decision 0072.
#[test]
fn prove_names_a_recursion_whose_measure_may_not_decrease() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-recursion-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-recursion-wrong.cpp:9: the decreases line may not decrease at this call.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{text}");
    let want = "model-recursion-wrong.cpp:14: the contract line has a form the translator cannot read.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{text}");
}

/// A `DAFNY` that does not run stops `prove` with a sentence that names it. No other Dafny takes its place, decision 0225.
#[test]
fn prove_stops_when_its_dafny_does_not_run() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("model-clamp.cpp");
    let plugin = plugin();
    let o = Command::new(env!("CARGO_BIN_EXE_cplusp"))
        .args(["prove", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"])
        .env("DAFNY", "/nonexistent/dafny")
        .current_dir(root())
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("/nonexistent/dafny"), "{}", stderr(&o));
    assert!(!stdout(&o).contains("ok: proved"), "{}", stdout(&o));
}

/// An empty `DAFNY` is a `DAFNY` that is not set, decision 0226.
#[test]
fn prove_reads_an_empty_dafny_as_unset() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("model-clamp.cpp");
    let plugin = plugin();
    let o = Command::new(env!("CARGO_BIN_EXE_cplusp"))
        .args(["prove", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"])
        .env("DAFNY", "")
        .current_dir(root())
        .output()
        .unwrap();
    assert!(!stderr(&o).contains("DAFNY names"), "{}", stderr(&o));
}

/// A time limit of 0 would let Dafny run with no limit, so `prove` refuses it, decision 0225.
#[test]
fn prove_refuses_a_time_limit_of_zero() {
    let o = cplusp(&["prove", "--time-limit", "0", "x.cpp"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("time-limit"), "{}", stderr(&o));
}

use super::*;

/// A global that a function lists is an implicit parameter: a reference parameter on a modifies line, a value on a reads line. A
/// call passes it on, a trusted function takes it, and a function can change only the globals it lists, decision 0173.
#[test]
fn a_global_is_an_implicit_parameter() {
    let dafny = dafny();
    require_clang_tidy();
    for name in ["model-state.cpp", "../../../../examples/global_state/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A body that undoes its write, a call too few, and a trusted callee whose requires line the caller does not meet each fail at
/// their lines. A lambda reads its own parameter, and a comparator reads the global after the write, decision 0173.
#[test]
fn a_global_keeps_the_contract_of_its_function() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-state-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        [
            "11: the ensures line may not hold on this return.",
            "28: the ensures line may not hold on this return.",
            "41: a requires line of the callee may not hold.",
            "55: the ensures line may not hold on this return.",
            "68: the ensures line may not hold on this return.",
        ],
        "{text}"
    );
    assert!(under(&text, "model-state-wrong.cpp:41: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-state-wrong.cpp:32: requires total < 1000")), "{text}");
}

/// A member function that lists a global, and a global of a type with no rule, are refused at the line that lists them. A reads
/// line that names no global keeps its old sentence, decision 0173.
#[test]
fn a_global_with_no_rule_is_refused() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-state-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "9: a const or virtual member function that lists a global: the translator has no rule for it yet.",
            "13: a global of this type: the translator has no rule for it yet.",
            "19: reads: the translator has no rule for it yet.",
        ],
        "{text}"
    );
}

/// A static member function is a free function with the name of its class. One that reads its globals and has one return has a
/// function twin, which a contract calls with the values before or after. The examples singleton and arena prove, decision 0174.
#[test]
fn a_static_member_function_is_a_free_function() {
    let dafny = dafny();
    require_clang_tidy();
    for name in ["model-static.cpp", "../../../../examples/singleton/example.cpp", "../../../../examples/arena/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A static member function keeps its contract: a body that adds too much, a call too few, an ensures line that calls a twin
/// before its requires line holds, and a caller that misses a requires line of a trusted static, decision 0174.
#[test]
fn a_static_keeps_the_contract_of_its_class() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-static-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        [
            "23: the ensures line may not hold on this return.",
            "39: the ensures line may not hold on this return.",
            "65: a requires line of the member function may not hold here.",
            "78: a requires line of the callee may not hold.",
            "99: the ensures line may not hold on this return.",
        ],
        "{text}"
    );
    assert!(under(&text, "model-static-wrong.cpp:78: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-static-wrong.cpp:58: requires valid() && 0 < size && size <= 4096 - used()")), "{text}");
}

/// A contract that calls a static which writes, a static whose contract names a field, and a bare call of a static outside its
/// class are refused, decision 0174.
#[test]
fn a_static_with_no_rule_is_refused() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-static-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "19: Tally::bump is no pure function. A contract calls a function with one return and no write.",
            "23: n_ in the contract is no parameter.",
            "31: valid is no function of the companion file.",
        ],
        "{text}"
    );
}

/// A valued enum class, the bit operators, a free operator, a duration, a std::array by value and as a result, and a const
/// reference to a scalar are integers or fixed sequences in the model. The examples enum_table, chrono, operator_overloading and
/// reinterpret_const_cast prove, decision 0175.
#[test]
fn types_that_are_an_integer_prove() {
    let dafny = dafny();
    require_clang_tidy();
    let examples = ["enum_table", "chrono", "operator_overloading", "reinterpret_const_cast"].map(|e| format!("../../../../examples/{e}/example.cpp"));
    for name in std::iter::once("model-int-types.cpp".to_string()).chain(examples) {
        let o = prove(&name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A bit operator that ands, a body that drops a flag, a brace list with a wrong value, a duration sum that drops a term, and a
/// free operator that adds the wrong field each fail at their return, decision 0175.
#[test]
fn types_that_are_an_integer_keep_their_contracts() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-int-types-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [12, 17, 22, 28, 40].map(|l| format!("{l}: the ensures line may not hold on this return."));
    assert_eq!(failed, want, "{text}");
}

/// A contract cast that can change the value, a duration other than milliseconds, a member operator, and a braced list that is
/// short of the extent are refused, decision 0175.
#[test]
fn types_that_are_an_integer_with_no_rule_are_refused() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-int-types-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "8: a static_cast in a contract that can change the value: the translator has no rule for it yet.",
            "14: std::chrono::seconds: the translator has no rule for it yet.",
            "24: CXXMethodDecl: the translator has no rule for it yet.",
            "31: a braced list of 2 values for a std::array of 3: the translator has no rule for it yet.",
        ],
        "{text}"
    );
}

/// A free function with one return and no write has a twin, and a contract calls it by its name. The example bit_flags proves,
/// decision 0176.
#[test]
fn a_free_function_twin_proves() {
    let dafny = dafny();
    require_clang_tidy();
    for name in ["model-free-twin.cpp", "../../../../examples/bit_flags/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A grant that drops the old flags, and a six that is seven, fail at their returns through the twins, decision 0176.
#[test]
fn a_free_function_twin_keeps_its_contract() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-free-twin-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [13, 24].map(|l| format!("{l}: the ensures line may not hold on this return."));
    assert_eq!(failed, want, "{text}");
}

/// A contract that calls a free function with two statements or with a reference parameter is refused with the one sentence,
/// decision 0176.
#[test]
fn a_free_function_with_no_twin_is_refused() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-free-twin-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "12: twice is no pure function. A contract calls a function with one return and no write.",
            "26: bump is no pure function. A contract calls a function with one return and no write.",
        ],
        "{text}"
    );
}

/// A name that is a function of the file and of the companion file is refused at the contract line that calls it, decision 0176.
#[test]
fn a_name_of_the_file_and_of_the_companion_file_is_refused() {
    require_clang_tidy();
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-free-twin-clash.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let want = "model-free-twin-clash.cpp:10: twice is a function of the file and of the companion file. Rename one.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 1, "{text}");
}

/// `x++` and `++x` inside an expression, a call that writes a value back inside an expression, and a call or a write on the right
/// of && or || or in a branch of ?: prove. The example evaluation_order proves, decision 0177.
#[test]
fn a_write_inside_an_expression_proves() {
    let dafny = dafny();
    require_clang_tidy();
    for name in ["model-writes.cpp", "../../../../examples/evaluation_order/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A next that gives the new value, a write on the right of && that runs whatever the left was, and a write on the right of ||
/// against a contract that says nothing changes, fail at their returns, decision 0177.
#[test]
fn a_write_inside_an_expression_keeps_its_contract() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-writes-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [10, 26, 33].map(|l| format!("{l}: the ensures line may not hold on this return."));
    assert_eq!(failed, want, "{text}");
}

/// A compound assignment as a value, a write in the condition of a loop, and a call in the condition of a loop are refused at
/// their lines, decision 0177.
#[test]
fn a_write_inside_an_expression_with_no_rule_is_refused() {
    let dafny = dafny();
    require_clang_tidy();
    let o = prove("model-writes-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let place = "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.";
    assert_eq!(
        refusals,
        [
            "8: BinaryOperator +=: the translator has no rule for it yet.".to_string(),
            "16: a write in the condition of a loop: the translator has no rule for it yet.".to_string(),
            format!("32: {place}"),
        ],
        "{text}"
    );
}

use super::*;

/// A struct with a destructor: the destructor runs at the end of the block of each local, in the reverse order, and before each
/// return after its value. A member that writes its object can list a global. The example classes_raii proves, decision 0178.
#[test]
fn a_struct_with_a_destructor_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-dtor.cpp", "../../../../examples/classes_raii/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A destructor that releases nothing, and a caller that forgets that the guard dies, fail at their returns. A destructor whose
/// requires line fails is reported at the line where its local dies, decision 0178.
#[test]
fn a_struct_with_a_destructor_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-dtor-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = ["23: the ensures line may not hold on this return.", "37: the ensures line may not hold on this return.", "46: a requires line of the callee may not hold."];
    assert_eq!(failed, want, "{text}");
}

/// A copy of a struct with a destructor, as a return of a local, a parameter, a field, a temporary and a container, a local whose
/// destructor has no contract, and a local in the head of a for, are refused, decision 0178.
#[test]
fn a_struct_with_a_destructor_and_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-dtor-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let copy = "a copy of a struct with a destructor: the translator has no rule for it yet.";
    let mut want: Vec<String> = [28, 32, 36, 69, 76, 80, 86, 94].map(|l| format!("{l}: {copy}")).to_vec();
    want.insert(3, "52: a destructor with no contract: the translator has no rule for it yet.".to_string());
    want.push("103: ForStmt: the translator has no rule for it yet.".to_string());
    want.push(format!("113: {copy}"));
    want.push("123: a call of a destructor: the translator has no rule for it yet.".to_string());
    assert_eq!(refusals, want, "{text}");
}

/// A constructor with a body, a move constructor, a `T&&` parameter of a struct and `std::move` of a struct prove, decision 0179.
/// The moved-from handle stays alive and releases nothing when it dies. A moved-from twin that stays open releases at the end of
/// its own block.
#[test]
fn a_move_of_a_struct_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-move.cpp", "../../../../examples/raii_handle/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A move constructor that leaves its source open fails its ensures line. The init list reads the source before the body writes
/// it, so a claim that the new cell holds the written value fails. A caller that forgets the release fails at its return, decision
/// 0179.
#[test]
fn a_move_of_a_struct_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-move-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = ["23: the ensures line may not hold on this return.", "57: the ensures line may not hold on this return.", "75: the ensures line may not hold on this return."];
    assert_eq!(failed, want, "{text}");
}

/// A field or `this` in the body of a constructor, a `T&&` parameter of a scalar, a move constructor in a struct with no destructor
/// or with a destructor `= default`, and a return that runs a copy or move constructor that the file only declares are refused,
/// decision 0179.
#[test]
fn a_move_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-move-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let field = "a field in the body of a constructor: the translator has no rule for it yet.";
    let mut want: Vec<String> = [9, 13, 18].map(|l| format!("{l}: {field}")).to_vec();
    want.push("31: int32_t &&: the translator has no rule for it yet.".to_string());
    want.push("42: a move constructor in a struct with no destructor: the translator has no rule for it yet.".to_string());
    want.push("56: a move constructor in a struct with no destructor: the translator has no rule for it yet.".to_string());
    want.push("82: a copy or a move by a constructor that the model cannot call: the translator has no rule for it yet.".to_string());
    want.push("103: a copy or a move by a constructor that the model cannot call: the translator has no rule for it yet.".to_string());
    assert_eq!(refusals, want, "{text}");
}

/// A vector by rvalue reference is a reference parameter, a move into a local vector gives the local the value, and `v(n, x)` is
/// a vector of n copies, decision 0185.
#[test]
fn a_vector_that_the_code_gives_up_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-vec-move.cpp", "../../../../examples/rvalue_references/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A moved-from vector has any value, so a claim about it fails, and a vector of n copies holds only the value it copies,
/// decision 0185.
#[test]
fn a_vector_that_the_code_gives_up_keeps_no_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-move-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = ["12", "18", "27", "35"].map(|l| format!("{l}: the ensures line may not hold on this return."));
    assert_eq!(failed, want, "{text}");
}

/// A team that loosens rvalue_references reads a vector after its move. The model keeps no value for a moved local, and the
/// caller gets back a vector with any value, so neither claim proves, decision 0185.
#[test]
fn a_vector_that_the_code_gives_up_has_no_value_without_the_gate() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-loosen-move.yaml");
    let o = prove("model-vec-move-loose.cpp", &["--policy", team.to_str().unwrap()], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["19: the ensures line may not hold on this return.", "26: the ensures line may not hold on this return."], "{text}");
}

/// The count and the value of `v(n, x)` are two arguments of one call, and the core checks them as it checks any call, so a write
/// and a read of one name in them is refused, decision 0185.
#[test]
fn a_vector_of_copies_keeps_the_order_check() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-vec-fill-order.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-vec-fill-order.cpp:8: k has a write and a read in one expression. C++ does not fix the order.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// A vector by rvalue reference that the modifies line does not name, `v(n)`, `v{a, b}`, and a move in a return or an assignment
/// are refused, decision 0185. A vector parameter by value proves since decision 0194.
#[test]
fn a_vector_that_the_code_gives_up_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-move-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let local = "a local vector has a rule only as a copy of a vector in scope.";
    let want = [
        "9: v is a reference parameter that the modifies line does not name.".to_string(),
        format!("22: {local}"),
        format!("28: {local}"),
        "36: CXXConstructExpr: the translator has no rule for it yet.".to_string(),
        "44: CXXOperatorCallExpr: the translator has no rule for it yet.".to_string(),
        "50: CXXTemporaryObjectExpr: the translator has no rule for it yet.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A class that holds a vector is a local, a copy and the object of its member functions. A constructor starts the vector with n
/// copies or empty, and a member function writes one element, decision 0187.
#[test]
fn a_class_that_holds_a_vector_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-bins.cpp", "../../../../examples/ring_buffer/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A write past the end of a vector field fails, each count starts at zero, a copy keeps the source as it was, and the init list runs
/// in the order of the fields, decision 0187.
#[test]
fn a_class_that_holds_a_vector_keeps_its_values() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-bins-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "30: the index may be out of range.",
        "41: the ensures line may not hold on this return.",
        "51: the ensures line may not hold on this return.",
        "60: the ensures line may not hold on this return.",
    ];
    assert_eq!(failed, want, "{text}");
}

/// A write through at and an assignment of a vector field, a struct that holds a vector in an optional, a vector or a unique_ptr,
/// and a vector field with a default member initializer are refused, decision 0187. A push_back of a field proves since decision
/// 0191.
#[test]
fn a_class_that_holds_a_vector_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-bins-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let holds = "a struct that holds a sequence has no rule yet in an optional, a pointer, a unique_ptr, or a vector that the code makes or writes.";
    let want = [
        "26: BinaryOperator =: the translator has no rule for it yet.".to_string(),
        "32: CXXOperatorCallExpr: the translator has no rule for it yet.".to_string(),
        format!("41: {holds}"),
        format!("47: {holds}"),
        format!("53: {holds}"),
        "61: CXXConstructorDecl: the translator has no rule for it yet.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A class template is a struct for each type that the file uses it at, with its member functions under the Dafny name of the
/// instance, decision 0188.
#[test]
fn a_class_template_proves_at_each_type() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-class-template.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-class-template.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(out).unwrap();
    for header in [
        "datatype S_Box'of'int32 = S_Box'of'int32(f_v_: int32)",
        "datatype S_Box'of'bool = S_Box'of'bool(f_v_: bool)",
        "datatype S_Pair'of'S_Point'bool = S_Pair'of'S_Point'bool(f_first: S_Point, f_second: bool)",
        "method c_Box'of'int32'set(v_this: S_Box'of'int32, v_v: int32) returns (v_this': S_Box'of'int32)",
        "method c_Box'of'bool'set(v_this: S_Box'of'bool, v_v: bool) returns (v_this': S_Box'of'bool)",
    ] {
        assert_eq!(text.matches(header).count(), 1, "{header}: {text}");
    }
}

/// A contract of a class template that holds at one type fails at another, and a caller of an instance proves what the instance
/// says, decision 0188.
#[test]
fn a_class_template_keeps_its_contract_at_each_type() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-class-template-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["18: the value may not fit int32_t.", "34: the ensures line may not hold on this return."], "{text}");
}

/// A class template with no instance, a type argument with no Dafny name, a member function template, a member function with a
/// contract that no instance makes, a contract that calls such a member by any path, and a member of an instance that is no struct
/// of the model are refused, decision 0188. A member that writes keeps its own sentence beside an instance. A contract that calls a
/// member of a plain struct that the file only declares names it by its name.
#[test]
fn a_class_template_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-class-template-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let no_model = "a call to Gauge<int>::valid, which has no model in view.";
    let no_instance = "a member function with no instance: the translator has no rule for it yet.";
    let method = "CXXMethodDecl: the translator has no rule for it yet.";
    let want = [
        "9: a class template with no instance: the translator has no rule for it yet.".to_string(),
        "15: a type argument with no Dafny name: the translator has no rule for it yet.".to_string(),
        "20: const Holder<std::vector<int32_t>> &: the translator has no rule for it yet.".to_string(),
        "33: a member function template: the translator has no rule for it yet.".to_string(),
        format!("48: {no_instance}"),
        format!("50: {no_model}"),
        format!("58: {no_model}"),
        format!("69: {no_model}"),
        format!("76: {no_model}"),
        "91: valid is no pure function. A contract calls a function with one return and no write.".to_string(),
        format!("106: {method}"),
        format!("115: {method}"),
        format!("125: {no_instance}"),
        "136: a class template with no instance: the translator has no rule for it yet.".to_string(),
        format!("149: {no_instance}"),
        format!("151: {no_instance}"),
        "155: a call to Meter<int>::value, which has no model in view.".to_string(),
        "161: a call to Meter<int>::operator(), which has no model in view.".to_string(),
        "172: a call to Probe::valid, which has no model in view.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A call of a plain member function is its function in place, of a field, of its own class, of a local, on the right of && and of
/// ||, in a branch of ?: and in a loop condition. A member function that calls only plain member functions is pure, and a contract
/// can call it, also when its own contract calls one, decisions 0189 and 0190.
#[test]
fn a_call_of_a_plain_member_function_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-plain-member.cpp", "../../../../examples/crtp/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A claim through a plain member function that does not hold fails, and Dafny checks the requires line of the function at each
/// call in code, decision 0189.
#[test]
fn a_call_of_a_plain_member_function_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-plain-member-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["15: the ensures line may not hold on this return.", "24: a requires line of the callee may not hold."], "{text}");
}

/// A member function whose body holds a call is no plain member function, so a member that calls it is no pure function. A plain
/// member function whose contract has no model stays a method, and so a member that calls it is no pure function. A call of a
/// virtual function of an interface is no call of a plain member function, decisions 0189 and 0190.
#[test]
fn a_call_of_a_member_function_that_is_not_plain_keeps_its_rules() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-plain-member-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "22: top is no pure function. A contract calls a function with one return and no write.",
        "32: the contract line has a form the translator cannot read.",
        "45: the contract line has a form the translator cannot read.",
        "52: g2 is no pure function. A contract calls a function with one return and no write.",
        "76: outer is no pure function. A contract calls a function with one return and no write.",
        "38: the ensures line may not hold on this return.",
        "49: the ensures line may not hold on this return.",
        "86: the prover cannot show that this ends.",
        "91: the prover cannot show that this ends.",
    ];
    assert_eq!(failed, want, "{text}");
    assert!(!text.contains("Dafny says"), "{text}");
}

/// A member function adds an element at the end of a vector field, takes the last one away and reads it. A `const T&` result of a
/// field, of an element or of the last element is its value, and a braced value at a `const T&` parameter is its value, decision
/// 0191.
#[test]
fn a_vector_field_that_grows_and_shrinks_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-vec-field.cpp", "../../../../examples/stack_template/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A pop and a read of the last element of a vector that can be empty fail at their line, and a pop takes the last element away,
/// decision 0191.
#[test]
fn a_vector_field_that_grows_and_shrinks_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-field-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    failed.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let want = [
        "17: a requires line of the callee may not hold.",
        "21: a requires line of the callee may not hold.",
        "35: the ensures line may not hold on this return.",
    ];
    assert_eq!(failed, want, "{text}");
    assert!(!text.contains("Dafny says"), "{text}");
}

/// front, emplace_back, a `const T&` result of a parameter and a pop of a local vector keep their sentence, decision 0191.
#[test]
fn a_vector_form_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-field-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "10: CXXMemberCallExpr: the translator has no rule for it yet.",
        "14: CXXMemberCallExpr: the translator has no rule for it yet.",
        "18: const int32_t &: the translator has no rule for it yet.",
        "29: CXXMemberCallExpr: the translator has no rule for it yet.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A node that the code makes with std::make_unique, writes through its pointer and moves into a field proves. So does a moved
/// parameter, which is null after its move, decision 0186.
#[test]
fn a_tree_that_the_code_builds_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-tree.cpp", "../../../../examples/tree_unique_ptr/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A new node holds the start value of each field, a write keeps the other fields, a moved pointer is in the field and not in the
/// parameter, a parameter moved in a branch can be null after it, and a write through a pointer that can be null fails, decision
/// 0186.
#[test]
fn a_tree_that_the_code_builds_keeps_what_it_wrote() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-tree-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let ensures = "the ensures line may not hold on this return.";
    let want = [
        format!("16: {ensures}"),
        format!("24: {ensures}"),
        format!("33: {ensures}"),
        "40: the optional may be empty or the pointer may be null here.".to_string(),
        format!("49: {ensures}"),
        format!("59: {ensures}"),
    ];
    assert_eq!(failed, want, "{text}");
}

/// A write through a parameter that the body does not move, a compound write, a write to a field of a field, std::make_unique of a
/// struct with an enum field, a field that starts from a call, an overflow or a write, or a field with no initializer, an
/// assignment of one unique_ptr to another, a return of nullptr, and a write through a parameter that moves only in a return are
/// refused, decision 0186.
#[test]
fn a_tree_that_the_code_builds_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-tree-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "27: p is a parameter. The translator writes only a local or a reference parameter.",
        "34: BinaryOperator +=: the translator has no rule for it yet.",
        "42: BinaryOperator =: the translator has no rule for it yet.",
        "48: a call to std::make_unique<Tagged>, which has no model in view.",
        "54: a call to std::make_unique<Seeded>, which has no model in view.",
        "62: CXXOperatorCallExpr: the translator has no rule for it yet.",
        "68: CXXConstructExpr: the translator has no rule for it yet.",
        "78: a call to std::make_unique<Over>, which has no model in view.",
        "92: a call to std::make_unique<Side>, which has no model in view.",
        "103: a call to std::make_unique<Bare>, which has no model in view.",
        "110: p is a parameter. The translator writes only a local or a reference parameter.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A local std::array from a brace list of its length is the sequence of the values. The code reads it, writes an element and
/// passes it to a span parameter, decision 0184.
#[test]
fn a_local_array_from_a_brace_list_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-array-local.cpp", "../../../../examples/strings/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// The values of a local array keep their order, and a write changes one element only, so a claim about another element fails,
/// decision 0184.
#[test]
fn a_local_array_keeps_its_values() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-array-local-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["8: the ensures line may not hold on this return.", "16: the ensures line may not hold on this return.", "35: the ensures line may not hold on this return.", "42: the index may be out of range."],
        "{text}"
    );
}

/// A brace list of another count, a local array from another array, and an array of a struct with a destructor, are refused,
/// decision 0184.
#[test]
fn a_local_array_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-array-local-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "7: a braced list of 2 values for a std::array of 3: the translator has no rule for it yet.",
        "13: a sequence is in the subset only as a parameter.",
        "25: a copy of a struct with a destructor: the translator has no rule for it yet.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A member function that writes its object and returns `*this` is a call that writes its object, and a chain runs its steps in
/// order on one object: a local, a temporary or a reference parameter, decision 0183.
#[test]
fn a_chain_of_calls_on_one_object_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-this.cpp", "../../../../examples/builder/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A chain runs each step, so a claim with a step left out fails at the return. A step whose requires line fails is named at the
/// line of the chain, decision 0183.
#[test]
fn a_chain_of_calls_keeps_each_step() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-this-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["26: the ensures line may not hold on this return.", "32: a requires line of the callee may not hold.", "39: a requires line of the callee may not hold."],
        "{text}"
    );
}

/// A reference result that is not `*this`, and the result of a call that gives back its object used as a value, are refused,
/// decision 0183. A step with no return or with a return that is not `*this`, a step that returns a copy, a temporary with a
/// destructor, and a chain where C++ may not run it once or inside an expression are refused too.
#[test]
fn a_chain_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-this-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let place = "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.";
    let want = [
        "19: a reference result that is not `*this`: the translator has no rule for it yet.".to_string(),
        "39: the result of a call that gives back its object, used as a value: the translator has no rule for it yet.".to_string(),
        "52: a reference result that is not `*this`: the translator has no rule for it yet.".to_string(),
        "60: UnaryOperator *: the translator has no rule for it yet.".to_string(),
        "66: a reference result that is not `*this`: the translator has no rule for it yet.".to_string(),
        "110: a copy of a struct with a destructor: the translator has no rule for it yet.".to_string(),
        format!("117: {place}"),
        format!("123: {place}"),
        format!("133: {place}"),
        format!("142: {place}"),
        "148: a chain of calls in the head of a for: the translator has no rule for it yet.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A temporary of a plain struct, bound to a `const T&` parameter, is its value, decision 0181.
#[test]
fn a_temporary_bound_to_a_const_reference_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-temp-ref.cpp", "../../../../examples/callbacks/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A temporary is the value it is built from, so a claim about another value fails at the return, decision 0181.
#[test]
fn a_temporary_bound_to_a_const_reference_keeps_its_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-temp-ref-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["16: the ensures line may not hold on this return."], "{text}");
}

/// A temporary in the return of a function that returns a reference has no rule, decision 0181. The temporary dies at the end of the
/// return, before the caller reads the reference.
#[test]
fn a_temporary_in_a_return_by_reference_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-temp-ref-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ") || l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let sentence = "a temporary in the return of a function that returns a reference: the translator has no rule for it yet.";
    assert_eq!(refused, [format!("16: {sentence}"), format!("33: {sentence}"), "56: MaterializeTemporaryExpr: the translator has no rule for it yet.".to_string()], "{text}");
}

/// Each instance of a function template is a function of the model with the contract of the template, and it proves on its own,
/// decision 0180. An instance has the Dafny name of the template, `'of'` and its Dafny types. Two functions with one such name are
/// numbered as overloads are.
#[test]
fn a_function_template_proves_at_each_type() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-template.cpp", "../../../../examples/templates/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-template.cpp", dir.path());
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let text = std::fs::read_to_string(out).unwrap();
    for header in [
        "method c_larger'of'int32(v_a: int32, v_b: int32) returns (result: int32)",
        "method c_larger'of'uint8(v_a: uint8, v_b: uint8) returns (result: uint8)",
        "method c_larger'of'int64(v_a: int64, v_b: int64) returns (result: int64)",
        "method c_largest'of'int64(v_a: int64, v_b: int64, v_c: int64) returns (result: int64)",
        "method c_first'of'int32'bool(v_a: int32, v_b: bool) returns (result: int32)",
    ] {
        assert_eq!(text.matches(header).count(), 1, "{header}: {text}");
    }
    assert!(text.contains("method c_pick'of'int32'1(") && text.contains("method c_pick'of'int32'2("), "{text}");
}

/// A contract of a template that holds at one type fails at another, and the shell names the type. An explicit instantiation is an
/// instance. A line that fails with one sentence in two instances prints once, and two sentences on one line both print, decision
/// 0180.
#[test]
fn a_function_template_keeps_its_contract_at_each_type() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-template-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    failed.sort_by_key(|l| (l.split(':').next().unwrap().parse::<u32>().unwrap(), l.to_string()));
    assert_eq!(
        failed,
        [
            "8: the value may not fit int32_t.",
            "14: the ensures line may not hold on this return.",
            "49: the ensures line may not hold on this return.",
            "58: the value may not fit int32_t.",
            "58: the value may not fit uint32_t.",
            "73: the value may not fit int32_t.",
            "73: the value may not fit int32_t.",
        ],
        "{text}"
    );
}

/// A member function template, an instance whose body has no rule, a template with no instance, a call of an instance that the
/// file only declares, and a type argument with no type of the model are refused. A refused instance has no contract for its
/// callers, decision 0180. A struct of a class template is a type of the model since decision 0188.
#[test]
fn a_function_template_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-template-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let want = [
        "9: a member function template: the translator has no rule for it yet.",
        "17: UnaryExprOrTypeTraitExpr: the translator has no rule for it yet.",
        "28: a function template with no instance: the translator has no rule for it yet.",
        "43: a call to larger<int>, which has no model in view.",
        "65: a function template with no instance: the translator has no rule for it yet.",
        "84: a type argument with no Dafny name: the translator has no rule for it yet.",
        "90: a call to count<std::vector<int>>, which has no model in view.",
    ];
    assert_eq!(refusals, want, "{text}");
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["22: the ensures line may not hold on this return."], "{text}");
    assert!(!text.contains("Dafny says"), "{text}");
}

/// A vector by value is a copy that the callee owns: it can add to it, write it and move it, and a constructor can move it into a
/// field. A copy leaves the caller's vector as it was, and a move gives the value, decision 0194.
#[test]
fn a_vector_by_value_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-vec-value.cpp", "../../../../examples/custom_range/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// A write of the callee to its copy is no write of the caller, and a false claim about a vector by value fails, decision 0194.
#[test]
fn a_vector_by_value_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-value-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = ["11", "17", "31"].map(|l| format!("{l}: the ensures line may not hold on this return."));
    assert_eq!(failed, want, "{text}");
}

/// A team that loosens rvalue_references reads a vector after it gives it to a parameter by value, in a constructor and in a call
/// that stands alone. The model keeps no value for it, so the claim does not prove. A unique_ptr that the same call moves is null,
/// decisions 0194 and 0195.
#[test]
fn a_vector_given_by_value_has_no_value_without_the_gate() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-loosen-move.yaml");
    let o = prove("model-vec-value-loose.cpp", &["--policy", team.to_str().unwrap()], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["25: the ensures line may not hold on this return.", "35: the ensures line may not hold on this return."], "{text}");
}

/// A function with a vector parameter by value is no pure function, so a contract cannot call it. A vector of bool by value keeps
/// its refusal, and so does a vector of a struct that holds a sequence, decision 0194. A move of a vector in a place with no rule
/// has its own sentence, decision 0195.
#[test]
fn a_vector_by_value_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-value-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let moved = "a std::move of a std::vector has no rule here. It has a rule as the start value of a local vector and in the init list of a constructor. It also has a rule at a parameter by value of a call. That call stands alone, is the value of a return, or is the start value of a local that is no vector.";
    let want = [
        "12: any is no pure function. A contract calls a function with one return and no write.".to_string(),
        "18: std::vector<bool>: the translator has no rule for it yet.".to_string(),
        format!("31: {moved}"),
        format!("40: {moved}"),
        format!("54: {moved}"),
        "63: a struct that holds a sequence has no rule yet in an optional, a pointer, a unique_ptr, or a vector that the code makes or writes.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A std::array field of a scalar is a sequence of its length in each object. The init list or a default member initializer gives
/// it zeros, a member function writes one element, and a caller reads it, decision 0196.
#[test]
fn a_class_that_holds_a_std_array_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-array-field.cpp", "../../../../examples/small_vector/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// The start value of a std::array field is zeros, Dafny checks each index in code and in a contract, and a false claim fails,
/// decision 0196.
#[test]
fn a_class_that_holds_a_std_array_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-array-field-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    failed.sort_by_key(|l| (l.split(':').next().unwrap().parse::<u32>().unwrap(), l.to_string()));
    let want = [
        "9: the ensures line may not hold on this return.",
        "12: the index may be out of range.",
        "13: the index may be out of range.",
        "17: the ensures line may not hold on this return.",
        "17: the index may be out of range.",
        "27: the ensures line may not hold on this return.",
    ];
    assert_eq!(failed, want, "{text}");
}

/// A std::array field with no start value is refused at its constructor, because C++ leaves its elements without a value,
/// decision 0196. The gate refuses it first under the row uninitialised_variables, but not in a class template, so the test reads
/// the model alone. A default member initializer with values keeps the sentence of today.
#[test]
fn a_std_array_field_with_no_start_value_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-array-field-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let none = "a std::array field with no start value: the translator has no rule for it yet.";
    let want = [format!("8: {none}"), "19: CXXConstructorDecl: the translator has no rule for it yet.".to_string(), format!("31: {none}")];
    assert_eq!(refused, want, "{text}");
}

/// A class keeps its data in a struct behind a unique_ptr field. It makes the struct with make_unique of its constructor, writes
/// through the pointer, defines its destructor = default out of line, and moves the pointer in a move constructor, written or
/// = default, decision 0197.
#[test]
fn the_pointer_to_implementation_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-pimpl.cpp", "../../../../examples/pimpl/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// make_unique gives the value of the constructor, a move leaves the source null, and Dafny checks that the pointer holds a
/// value at each write through it, decision 0197. The source is null right after the init that moves it, decision 0198.
#[test]
fn the_pointer_to_implementation_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pimpl-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    failed.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    let want = [
        "14: the ensures line may not hold on this return.",
        "20: the ensures line may not hold on this return.",
        "34: the optional may be empty or the pointer may be null here.",
        "51: the ensures line may not hold on this return.",
        "74: the optional may be empty or the pointer may be null here.",
    ];
    assert_eq!(failed, want, "{text}");
}

/// A move constructor = default of a struct with a field that is no scalar and no unique_ptr, and a write through a unique_ptr
/// field of a parameter, keep their sentences, decision 0197. So does a move in a move constructor with a second parameter,
/// decision 0198.
#[test]
fn the_pointer_to_implementation_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pimpl-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "29: CXXConstructorDecl: the translator has no rule for it yet.",
        "41: BinaryOperator =: the translator has no rule for it yet.",
        "52: a call to std::move<std::unique_ptr<Cell> &>, which has no model in view.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A plain member function can hold apply lines, so a member function that calls it has a function in the model, decision 0211.
#[test]
fn a_plain_member_function_with_apply_lines_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-plain-apply.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-plain-apply-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["29: the ensures line may not hold on this return."], "{text}");
}

/// A std::move of a trivially copyable value is the value, and a constructor template has an instance for each type, decision 0212.
#[test]
fn a_move_of_a_value_and_a_constructor_template_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-move-value.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-move-value-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["49: the ensures line may not hold on this return.", "56: the ensures line may not hold on this return."], "{text}");
}

/// A std::move of a value that is not trivially copyable keeps its sentence, decision 0212.
#[test]
fn a_move_of_a_value_that_is_not_trivially_copyable_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-move-value-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refused, ["13: a call to std::move<Bag &>, which has no model in view."], "{text}");
}

/// The function of a pure member function keeps its ensures lines, so the check of an override two calls from the bound proves,
/// decision 0213.
#[test]
fn a_function_keeps_its_ensures_lines() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-function-ensures.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A member function template counts as an overload of its name, so a contract that calls the name is refused, decision 0215.
#[test]
fn a_contract_that_calls_a_name_of_a_member_template_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-member-template-overload.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refused, ["16: get is no pure function. A contract calls a function with one return and no write."], "{text}");
}

/// An ensures line that calls a function stays on the method, so two functions whose ensures lines call each other prove,
/// decision 0215.
#[test]
fn an_ensures_line_that_calls_a_function_stays_on_the_method() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-function-ensures-cycle.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A static member function template has no rule yet, and its sentence says so, decision 0215.
#[test]
fn a_static_member_template_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-member-template-static.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert!(refused.contains(&"13: a member function template: the translator has no rule for it yet."), "{text}");
    assert!(!text.contains("a name with a character Dafny cannot read"), "{text}");
}

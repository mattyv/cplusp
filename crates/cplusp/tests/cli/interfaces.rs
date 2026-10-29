use super::*;

/// A call through const Shape& reads the contract of Shape::corners, a call on const Square& reads the override, and each override
/// is checked against the contract of the interface, decision 0165. prove names the trust once for each interface.
#[test]
fn a_call_through_an_interface_proves_and_each_override_is_checked() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.last(), Some(&"ok: proved"), "{text}");
    assert_eq!(lines.iter().filter(|l| **l == SHAPE_AXIOM).count(), 1, "{text}");
    // A model with no interface names no axiom of one.
    let o = prove("model-method.cpp", &[], &dafny);
    assert!(!stdout(&o).contains("Axiom: model:"), "{}", stdout(&o));
}

/// An override that requires more than the interface, and one that promises less, each fail at the override with their own
/// sentence and the contract line of the interface under it. A class over two interfaces is checked against each, decision 0165.
#[test]
fn an_override_that_breaks_the_contract_of_the_interface_fails_at_its_line() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    // One line for the interface, though two classes derive from it.
    assert_eq!(text.lines().filter(|l| *l == SHAPE_AXIOM).count(), 1, "{text}");
    let found = blocks(&text);
    let broken = |head: &str, clause: &str| {
        found.iter().filter(|(h, under)| h.ends_with(head) && under.iter().any(|u| u.starts_with("  The contract line: ") && u.ends_with(clause))).count()
    };
    let more = "model-virtual-wrong.cpp:17: the override may require more than Shape::corners.";
    assert_eq!(broken(more, "model-virtual-wrong.cpp:7: requires 0 <= scale && scale <= 100"), 1, "{text}");
    let less = "model-virtual-wrong.cpp:25: the override may not keep the promise of Shape::corners.";
    assert_eq!(broken(less, "model-virtual-wrong.cpp:8: ensures result >= 3 * scale"), 1, "{text}");
    // A class over two interfaces has a check for each.
    let red = "model-virtual-wrong.cpp:42: the override may not keep the promise of Colored::red.";
    assert_eq!(broken(red, "model-virtual-wrong.cpp:31: ensures 0 <= result && result <= 255"), 1, "{text}");
    assert_eq!(found.len(), 3, "{text}");
}

/// A requires line of an interface that may read out of range fails once, at that line. The check of the override reads the same
/// line, and adds no failure of its own, decision 0165.
#[test]
fn a_requires_line_of_an_interface_that_fails_fails_once() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-index.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["8: the index may be out of range."], "{text}");
}

/// A class over an interface that is not final, a final class with no override, and an override with no function in the model are
/// refused at the line of the class. A pointer to an interface has no rule, and an interface with two virtual functions of one name
/// is refused at its line. A class that is not final is no type of a parameter. A call with the name of the interface and a body
/// of a pure virtual function have no rule. A call through the interface still translates, decision 0165.
#[test]
fn a_class_over_an_interface_with_no_rule_is_refused_at_its_line() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-virtual-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        refusals,
        [
            "12: Open derives from an interface and is not final. Mark it final.",
            "18: Half has no override of Shape::corners.",
            "23: the override of Shape::corners in Two has no function in the model, so the translator cannot check it.",
            "38: const Shape *: the translator has no rule for it yet.",
            "52: Bell has no override of Sound::pitch.",
            "62: const Open &: the translator has no rule for it yet.",
            "69: a qualified call of a virtual function: the translator has no rule for it yet.",
            "73: a body of a pure virtual function: the translator has no rule for it yet.",
        ],
        "{text}"
    );
    let model = std::fs::read_to_string(&out).unwrap();
    assert!(model.contains("method c_count("), "{model}");
}

/// The example single_inheritance proves: an interface, a final class over it, and a call through each, decision 0165.
#[test]
fn the_virtual_examples_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/single_inheritance/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A contract of an interface calls valid(), a caller reads s.valid() and s.apply(x) in its contract, a constructor builds a class
/// over the interface, and a final class goes to a parameter of the interface. The caller knows the value of each call from the
/// upcast, decision 0166.
#[test]
fn a_virtual_call_in_a_contract_and_an_upcast_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-call.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A caller that claims more than the interface fails at its return, a contract call outside the requires lines of the interface
/// fails at the contract line, and an object whose valid() is false fails at the call that upcasts it, decision 0166.
#[test]
fn a_virtual_call_and_an_upcast_keep_the_contract_of_the_interface() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-call-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let found = blocks(&text);
    let broken = |head: &str, clause: &str| {
        found.iter().filter(|(h, under)| h.ends_with(head) && under.iter().any(|u| u.starts_with("  The contract line: ") && u.ends_with(clause))).count()
    };
    let ensures = "model-virtual-call-wrong.cpp:24: the ensures line may not hold on this return.";
    assert_eq!(broken(ensures, "model-virtual-call-wrong.cpp:22: ensures result <= 1000"), 1, "{text}");
    let member = "model-virtual-call-wrong.cpp:28: a requires line of the member function may not hold here.";
    assert_eq!(broken(member, "model-virtual-call-wrong.cpp:7: requires valid() && 0 <= x && x <= 1000"), 1, "{text}");
    let callee = "model-virtual-call-wrong.cpp:36: a requires line of the callee may not hold.";
    assert_eq!(broken(callee, "model-virtual-call-wrong.cpp:21: requires s.valid() && 0 <= x && x <= 1000"), 1, "{text}");
    assert_eq!(found.len(), 3, "{text}");
}

/// A contract of an interface that reads a virtual function declared after it, or the function itself, is refused at the contract
/// line, and the class over that interface has no upcast. A pure virtual function that gives no value has no rule. A pure virtual
/// function is a function of the model with no body, decision 0166.
#[test]
fn a_contract_of_an_interface_reads_only_the_functions_above_it() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-virtual-call-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        refusals,
        [
            "6: the contract of Late::apply reads Late::ready, which comes later in Late. Declare Late::ready first.",
            "26: the contract of Loop::size reads Loop::size itself. The translator has no rule for it yet.",
        ],
        "{text}"
    );
    let model = std::fs::read_to_string(&out).unwrap();
    assert!(!model.contains("f_Soon'Late"), "{model}");
    assert!(model.contains("function {:axiom} c_Late'ready'("), "{model}");
}

/// A call that upcasts a class with no check stops Dafny on the name of the upcast, after the refusal of the class, decision 0166.
#[test]
fn an_upcast_of_a_class_with_no_check_is_not_in_the_model() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-call-unchecked.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let unchecked = "10: the override of Shape::corners in Two has no function in the model, so the translator cannot check it.";
    assert_eq!(refusals, [unchecked, "27: Dafny says: unresolved identifier: f_Two'Shape."], "{text}");
}

/// The Axiom line names the interface by its C++ name. Two interfaces of one name show their full names, decision 0166.
#[test]
fn the_axiom_line_of_an_interface_names_it_in_cpp() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-names.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let axioms: Vec<&str> = text.lines().filter(|l| l.starts_with("Axiom: model: ")).collect();
    let line = |n: &str| format!("Axiom: model: {n}: a call through {n} runs an override that keeps the contract of {n}, C++23 [class.virtual]. Each override of {n} in this file is checked against that contract.");
    assert_eq!(axioms, [line("a::Shape"), line("b::Shape")], "{text}");
}

/// An apply line of MulBound gives the bound of a product of two names, in a free function and in a pure override, whose function
/// and check call the lemma too. A caller knows the value of the override, decision 0167.
#[test]
fn the_bound_of_a_product_proves_with_mul_bound() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-product.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    // MulBound is a lemma that Dafny proves, so it names no axiom.
    assert!(!text.contains("MulBound"), "{text}");
    // The check of the override calls the lemma, as its function does.
    let dir = tempfile::tempdir().unwrap();
    let (_, out) = model("model-product.cpp", dir.path());
    let model = std::fs::read_to_string(&out).unwrap();
    let check = model.split_once("lemma c_Rect'area'check'Shape").map(|(_, rest)| rest.split_once("\n}").map_or(rest, |(body, _)| body)).unwrap_or("");
    assert!(check.contains("MulBound("), "{model}");
}

/// An apply line of MulBound whose bounds the requires lines do not give fails at its line, once, in a free function and in a pure
/// override, decision 0167.
#[test]
fn mul_bound_with_a_bound_that_does_not_hold_fails_at_its_line() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-product-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["7: a requires line of the callee may not hold.", "27: a requires line of the callee may not hold."], "{text}");
}

/// The examples whose overrides bound a product prove with an apply line of MulBound, decision 0167.
#[test]
fn the_product_examples_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for example in ["strategy"] {
        let o = prove(&format!("../../../../examples/{example}/example.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{example}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{example}: {text}");
    }
}

/// A hint that holds in the method of an override and fails in its check means that the override requires more than the
/// interface. prove says so at the override, with the requires line of the override, also when another function fails with the
/// words of the hint, decision 0167.
#[test]
fn a_hint_that_fails_only_in_the_check_names_the_requires_half() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let more = "16: the override may require more than Shape::area.";
    for (name, want) in [("model-product-more.cpp", vec![more]), ("model-product-more-twin.cpp", vec![more, "27: a requires line of the callee may not hold."])] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
        assert_eq!(failed, want, "{name}: {text}");
        let head = format!("{name}:{more}");
        assert!(under(&text, &head).iter().any(|l| l.starts_with("  The contract line: ") && l.ends_with(&format!("{name}:14: requires valid() && w_ <= 500"))), "{name}: {text}");
    }
}

/// A unique_ptr of an interface made by std::make_unique of a final class, a call through it in code and in a contract, a local
/// that a call sets, and a parameter by const reference prove, decision 0168.
#[test]
fn a_unique_ptr_of_an_interface_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-iface.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A call through a unique_ptr of an interface that may be null fails at the call with the sentence of 0075, and one whose object
/// may not be valid fails with the requires line of the interface, decision 0168.
#[test]
fn a_call_through_a_unique_ptr_of_an_interface_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-iface-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["16: the optional may be empty or the pointer may be null here.", "22: a requires line of the callee may not hold."], "{text}");
    assert!(under(&text, "model-unique-iface-wrong.cpp:22: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-unique-iface-wrong.cpp:8: requires valid()")), "{text}");
}

/// The example factory makes a shape with std::make_unique and reads it through std::unique_ptr<Shape>, decision 0168.
#[test]
fn the_unique_ptr_examples_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/factory/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A make_unique of a class that is not final or has no check, a unique_ptr of a final class, a move, the return of a local
/// unique_ptr, and a unique_ptr of a class from a call as one of its interface have no rule, so no second owner and no moved-from
/// pointer reaches the model, decision 0168.
#[test]
fn a_unique_ptr_of_an_interface_has_one_owner_that_only_reads() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-iface-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "12: Open derives from an interface and is not final. Mark it final.",
            "24: the override of Shape::area in Two has no function in the model, so the translator cannot check it.",
            "40: a call to std::make_unique<Open>, which has no model in view.",
            "44: Dafny says: unresolved identifier: f_Two'Shape.",
            "48: a call to std::make_unique<Square>, which has no model in view.",
            "54: a call to std::move<std::unique_ptr<Shape> &>, which has no model in view.",
            "59: CXXConstructExpr: the translator has no rule for it yet.",
            "63: a call to std::make_unique<Square>, which has no model in view.",
            "67: a std::unique_ptr of a class as a std::unique_ptr of its interface: the translator has no rule for it yet.",
        ],
        "{text}"
    );
}

/// A virtual function that writes its object runs through a reference of the interface on the modifies line and through a local
/// unique_ptr, which takes the new value. Each override is checked on the contracts, decision 0169.
#[test]
fn a_virtual_function_that_writes_its_object_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-virtual-mut.cpp", "model-virtual-mut-ref.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// An override that writes and promises less, one that requires more, and a read of the value before the write each fail at their
/// line, decision 0169.
#[test]
fn an_override_that_writes_keeps_the_contract_of_the_interface() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-virtual-mut-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let found = blocks(&text);
    let broken = |head: &str, clause: &str| {
        found.iter().filter(|(h, under)| h.ends_with(head) && under.iter().any(|u| u.starts_with("  The contract line: ") && u.ends_with(clause))).count()
    };
    let less = "model-virtual-mut-wrong.cpp:26: the override may not keep the promise of Observer::on_change.";
    assert_eq!(broken(less, "model-virtual-mut-wrong.cpp:12: ensures valid() && seen() == old(seen()) + 1"), 1, "{text}");
    let more = "model-virtual-mut-wrong.cpp:44: the override may require more than Observer::on_change.";
    assert_eq!(broken(more, "model-virtual-mut-wrong.cpp:11: requires valid() && seen() < 1000"), 1, "{text}");
    assert!(found.iter().any(|(h, _)| h.ends_with("model-virtual-mut-wrong.cpp:55: the assert line may not hold.")), "{text}");
    assert_eq!(found.len(), 3, "{text}");
}

/// A class at a reference of its interface, a write through the value of a unique_ptr, an override with no method in the model, and
/// a reference parameter of an interface function that no modifies line names are refused at their lines, decision 0169.
#[test]
fn a_write_through_an_interface_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-virtual-mut-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "44: a class as a reference to its interface: the translator has no rule for it yet.",
            "49: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
            "53: the override of Observer::on_change in Loud has no method in the model, so the translator cannot check it.",
            "63: DoStmt: the translator has no rule for it yet.",
            "83: c is a reference parameter that the modifies line does not name.",
        ],
        "{text}"
    );
}

/// A vector of unique_ptr of an interface reads through each element, a local starts empty and grows by push_back, and a call
/// that writes an element writes it back, also through a local passed by reference, decision 0170.
#[test]
fn a_vector_of_unique_ptr_of_an_interface_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-vec-unique.cpp", "model-vec-unique-mut.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// An element that may be null, an index that may be out of range, and a read of an element before its write fail at their lines,
/// decision 0170.
#[test]
fn a_vector_of_unique_ptr_keeps_its_bounds_and_its_values() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-unique-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        ["16: the optional may be empty or the pointer may be null here.", "21: the index may be out of range.", "39: the assert line may not hold."],
        "{text}"
    );
}

/// An assignment to an element, a range-for, a write through `*v[i]`, a vector of unique_ptr as a result, and an index that the call
/// writes are refused at their lines, decision 0170.
#[test]
fn a_vector_of_unique_ptr_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-vec-unique-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "47: an assignment to a unique_ptr element: the translator has no rule for it yet.",
            "54: a range-for over a vector of unique_ptr: the translator has no rule for it yet.",
            "63: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
            "66: std::vector<std::unique_ptr<Observer>>: the translator has no rule for it yet.",
            "82: the index reads a value that the call writes: the translator has no rule for it yet.",
        ],
        "{text}"
    );
}

/// The examples shape_area_sum and command keep their objects in a vector of unique_ptr of an interface, decision 0170.
#[test]
fn the_vector_examples_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for example in ["shape_area_sum", "command"] {
        let o = prove(&format!("../../../../examples/{example}/example.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{example}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{example}: {text}");
    }
}

/// A unique_ptr of an interface as a field and as a parameter by value proves. A local moves into a constructor, into a call, into
/// another local and into std::make_unique, and a return moves a local out. A moved local is null after its statement, decision
/// 0171.
#[test]
fn a_unique_ptr_field_and_a_move_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-field.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A call through a unique_ptr field keeps the null check of 0075 and the requires lines of the interface. A moved local meets the
/// requires lines of the constructor that takes it, decision 0171.
#[test]
fn a_call_through_a_unique_ptr_field_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-field-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        [
            "22: the optional may be empty or the pointer may be null here.",
            "26: a requires line of the callee may not hold.",
            "47: a requires line of the callee may not hold.",
        ],
        "{text}"
    );
    assert!(under(&text, "model-unique-field-wrong.cpp:26: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-unique-field-wrong.cpp:10: requires valid() && 0 <= x && x <= 1000")), "{text}");
    assert!(under(&text, "model-unique-field-wrong.cpp:47: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-unique-field-wrong.cpp:16: requires inner != nullptr && inner->valid()")), "{text}");
}

/// Two moves of one local in one statement, a move and a read of one local in one call, a move in a condition, a move of an element
/// of a vector, a move into std::make_unique at a parameter by const reference, and a call that writes through a field have no
/// rule, so no two names share one object and no read sees a moved local, decision 0171. A move of a parameter in a call has a rule
/// since decision 0186.
#[test]
fn a_moved_unique_ptr_has_one_owner() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique-field-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "37: a moves and is read in one statement. C++ does not fix the order.",
            "43: a moves and is read in one statement. C++ does not fix the order.",
            "54: a std::move of a std::unique_ptr has no rule here. It has a rule only in a call that stands alone, the start value of a local, a return or a field write.",
            "62: a call to std::move<std::unique_ptr<Component> &>, which has no model in view.",
            "67: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
            "87: a call to std::move<std::unique_ptr<Component> &>, which has no model in view.",
        ],
        "{text}"
    );
}

/// Pure overrides that call the interface through a field, with a local before the return, prove with their checks, and so does a
/// call of a virtual function on the right of &&, decision 0172.
#[test]
fn a_pure_override_that_calls_its_field_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure-calls.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A pure override that reads its field with no null guard fails at its return. A call on the right of && checks the requires
/// lines of the interface. A bound that the decorator does not give fails at the return, decision 0172.
#[test]
fn a_pure_override_keeps_the_checks_of_its_calls() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure-calls-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(
        failed,
        [
            "59: the optional may be empty or the pointer may be null here.",
            "70: a requires line of the callee may not hold.",
            "79: the ensures line may not hold on this return.",
        ],
        "{text}"
    );
    assert!(under(&text, "model-pure-calls-wrong.cpp:70: a requires line of the callee may not hold.").iter().any(|l| l.ends_with("model-pure-calls-wrong.cpp:10: requires valid() && 0 <= x <= 1000")), "{text}");
}

/// An override whose body writes a local, or calls a member function of its own class that is no plain member function, has no
/// function in the model, so its class is refused, decisions 0172 and 0189.
#[test]
fn an_override_that_is_no_pure_body_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure-calls-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    refusals.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(
        refusals,
        [
            "12: the override of Component::cost in Written has no function in the model, so the translator cannot check it.",
            "26: the override of Component::valid in Own has no function in the model, so the translator cannot check it.",
            "34: valid is no pure function. A contract calls a function with one return and no write.",
        ],
        "{text}"
    );
}

/// The example decorator proves with decisions 0171 and 0172.
#[test]
fn the_decorator_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/decorator/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A const virtual function of an interface gives back a unique_ptr of the interface, and each override checks against its
/// contract. A context replaces the state that it owns with the next one and proves from the interface alone. A pure body can
/// return early, decision 0199.
#[test]
fn a_state_that_gives_the_next_state_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for name in ["model-next-state.cpp", "../../../../examples/state_object/example.cpp"] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{name}: {text}");
    }
}

/// An override that gives the wrong next state breaks the promise of the interface, and a pure body with an early return keeps
/// its contract, decision 0199.
#[test]
fn a_state_that_gives_the_next_state_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-next-state-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let mut failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    failed.sort_by_key(|l| l.split(':').next().unwrap().parse::<u32>().unwrap());
    assert_eq!(failed, ["22: the override may not keep the promise of Signal::next.", "36: the ensures line may not hold on this return."], "{text}");
}

/// An early return in a body that writes a local is no pure body, and a write of a unique_ptr field from a move of a local keeps
/// its sentence, decision 0199.
#[test]
fn a_state_that_gives_the_next_state_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-next-state-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "19: step is no pure function. A contract calls a function with one return and no write.",
        "36: CXXOperatorCallExpr: the translator has no rule for it yet.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A final class over a base with data and an interface proves, and a call of a `const` member function of the base reads in code and
/// in a contract, decision 0201.
#[test]
fn a_base_class_with_data_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-data-base.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A false claim through a member function of the base fails, decision 0201.
#[test]
fn a_base_class_with_data_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-data-base-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["20: the ensures line may not hold on this return.", "26: the ensures line may not hold on this return."], "{text}");
}

/// A field of the base, a change into the base and a call of a member function of the base that is not const have no rule yet, decision 0201.
#[test]
fn a_base_class_with_data_with_no_rule_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-data-base-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let want = [
        "29: a field of the base Spot: the translator has no rule for it yet.",
        "40: a change of Box into its base Tag, which has data: the translator has no rule for it yet.",
        "46: a call of a member function of the base Tag that is not const: the translator has no rule for it yet.",
    ];
    assert_eq!(refused, want, "{text}");
}

/// A field of a base with data through the class has no rule, in each form of a write and a read, and each sentence names the
/// classes by their plain names, decision 0203.
#[test]
fn a_field_of_the_base_is_refused_in_each_form() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-data-base-field.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refused: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let field = "a field of the base P: the translator has no rule for it yet.";
    let want = [
        format!("12: {field}"),
        format!("14: {field}"),
        format!("20: {field}"),
        format!("26: {field}"),
        format!("34: {field}"),
        format!("40: {field}"),
        "52: a change of R into its base P, which has data: the translator has no rule for it yet.".to_string(),
        "66: a field of the base P2: the translator has no rule for it yet.".to_string(),
    ];
    assert_eq!(refused, want, "{text}");
}

/// A call in code of a member function of the base keeps its contract, with a requires line, an overload and a trusted
/// member, decision 0203.
#[test]
fn a_call_of_the_base_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-data-base-calls.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-data-base-calls-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["21: the ensures line may not hold on this return.", "27: a requires line of the callee may not hold."], "{text}");
}

/// The failures of a fixture, each as `LINE: sentence`.
fn failures(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect()
}

/// A local of a final class can be the argument for a reference to its interface, and the caller reads it after the call. `prove`
/// names the assumption on an Axiom line, decision 0208.
#[test]
fn a_local_through_a_reference_to_its_interface_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-iface-local.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l == "Axiom: model: Total: a call through a reference to Sink leaves an object of Total, C++23 [class.virtual]."), "{text}");
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-iface-local-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["43: the ensures line may not hold on this return."], "{text}");
}

/// A field and a parameter of the class as the argument for a reference to the interface have no rule yet, decision 0208.
#[test]
fn a_field_through_a_reference_to_its_interface_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-iface-local-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let sentence = "a class as a reference to its interface: the translator has no rule for it yet.";
    assert_eq!(failures(&text), [format!("43: {sentence}"), format!("50: {sentence}")], "{text}");
}

/// A const virtual function that gives no value writes its reference parameter, and its override is checked, decision 0209.
#[test]
fn a_const_virtual_function_that_writes_a_parameter_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-const-void.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-const-void-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["29: the override may not keep the promise of Source::give."], "{text}");
}

/// Two virtual functions of one name each have their override, and each is checked, decision 0210. A contract cannot call one
/// by its name yet.
#[test]
fn two_virtual_functions_of_one_name_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-overload.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-overload-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["21: the override may not keep the promise of Look::see."], "{text}");
    let o = prove("model-overload-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["29: see is no pure function. A contract calls a function with one return and no write."], "{text}");
}

/// `*this` is the object, as an argument for a const reference or a value, and as a reference that is not const it has no rule,
/// decision 0214.
#[test]
fn the_object_as_an_argument_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-this-arg.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-this-arg-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["30: the ensures line may not hold on this return."], "{text}");
    let o = prove("model-this-arg-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["18: `*this` as a reference that is not const: the translator has no rule for it yet."], "{text}");
}

/// A local through a reference to its interface needs a final class over each interface of the file, decision 0217.
#[test]
fn a_local_through_its_interface_with_an_unbacked_interface_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-iface-local-unbacked.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["42: a class as a reference to its interface: the translator has no rule for it yet."], "{text}");
}

/// `*this` for a reference that is not const has no rule in a member call either, decision 0217.
#[test]
fn the_object_as_an_argument_of_a_member_call_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-this-arg-member-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["22: `*this` as a reference that is not const: the translator has no rule for it yet."], "{text}");
}

/// A sentence names one of two virtual functions of one name by its plain name, and a contract that calls such a name is no pure
/// function, decision 0217.
#[test]
fn a_name_of_two_virtual_functions_stays_plain_in_each_sentence() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-overload-names.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = [
        "7: the contract of Late::apply reads Late::ready, which comes later in Late. Declare Late::ready first.",
        "29: size is no pure function. A contract calls a function with one return and no write.",
    ];
    assert_eq!(failures(&text), want, "{text}");
}

/// A const and a non-const virtual function of one name are two overloads, so each override is checked against its own function,
/// decision 0217.
#[test]
fn a_const_and_a_non_const_virtual_function_of_one_name_are_two_overloads() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-overload-const.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(failures(&text), ["18: the override may not keep the promise of Look::see."], "{text}");
}

/// A call through an interface that can run an override of it again before it returns is refused, in each form that reaches the
/// override: through `*this`, through a write-back of a local, and through a chain of calls, decision 0218. The refused function has
/// no contract in the model, so the override that calls it is not proved either.
#[test]
fn a_call_through_an_interface_that_can_come_back_is_refused() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let fill = "the call of Filler::fill can run Filler::fill again before it returns: the translator has no rule for it yet.";
    let poke = "the call of Poker::poke can run Poker::poke again before it returns: the translator has no rule for it yet.";
    let ret = "the ensures line may not hold on this return.";
    for (name, want) in [
        ("model-iface-recursion-refuse.cpp", [format!("51: {fill}"), format!("54: {ret}")]),
        ("model-iface-recursion-down.cpp", [format!("50: {poke}"), format!("53: {ret}")]),
        ("model-iface-recursion-chain.cpp", [format!("51: {fill}"), format!("57: {ret}")]),
    ] {
        let o = prove(name, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(failures(&text), want, "{name}: {text}");
    }
}

/// A write-back through an interface in a file where an interface has no final class is refused in each place of a body, so the
/// walker of 0217 finds each one, decision 0218.
#[test]
fn an_unbacked_write_back_is_refused_in_each_place_of_a_body() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-iface-local-unbacked-places.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let iface = "a class as a reference to its interface: the translator has no rule for it yet.";
    let want = [
        format!("62: {iface}"),
        format!("74: {iface}"),
        format!("86: {iface}"),
        format!("96: {iface}"),
        format!("107: {iface}"),
        format!("114: {iface}"),
        "121: a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.".to_string(),
        "128: the call writes a value back, and the translator writes back only to a local or a reference parameter.".to_string(),
    ];
    assert_eq!(failures(&text), want, "{text}");
}

/// A class can hold a vector of unique_ptr of an interface, add to it with push_back of a move, and call each element, decision
/// 0204.
#[test]
fn a_list_of_owned_objects_as_a_field_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for file in ["model-owned-list.cpp", "../../../../examples/observer/example.cpp"] {
        let o = prove(file, &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(0), "{file}: stdout: {text} stderr: {}", stderr(&o));
        assert_eq!(text.lines().last(), Some("ok: proved"), "{file}: {text}");
    }
}

/// A false claim through a vector of unique_ptr of an interface in a field fails, decision 0204.
#[test]
fn a_list_of_owned_objects_as_a_field_keeps_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-owned-list-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["50: the ensures line may not hold on this return.", "61: the ensures line may not hold on this return."], "{text}");
}

/// A push of `std::move(o)` leaves `o` null, in a field, in a vector by reference and in a local vector, decision 0204.
#[test]
fn a_push_of_a_move_leaves_the_name_null() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-owned-push.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-owned-push-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ") || l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let sentence = "the ensures line may not hold on this return.";
    assert_eq!(failed, [format!("20: {sentence}"), format!("32: {sentence}"), format!("43: {sentence}")], "{text}");
}

/// The example `visitor` proves: a double dispatch through two interfaces, with a local visitor written back through its interface,
/// decisions 0208 and 0218.
#[test]
fn the_visitor_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/visitor/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert!(text.lines().any(|l| l == "Axiom: model: AreaSum: a call through a reference to Visitor leaves an object of AreaSum, C++23 [class.virtual]."), "{text}");
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

use super::*;

// ------------------------------------------------------------------ markers, decision 0039

/// The plugin reads the markers of include/cplusp.h. A finding takes the kind of the function that holds it, and the core decides
/// what each kind keeps. Every finding stands in verified code. A finding of a Trusted only row goes in a trusted body, here `new`
/// and a stream, and a ban stands there, here `goto`. Nothing of a row stands in plain code. Verified code may not call plain code.
#[test]
fn a_finding_takes_the_kind_of_the_function_that_holds_it() {
    require_clang_tidy();
    let f = fixture("markers.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> =
        [("goto", 17), ("goto", 18), ("marker", 34), ("plain_int", 47)].into_iter().map(|(r, n)| (r.to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
    assert!(out.contains("marker: verified code calls legacy_parse, which is plain. Give it a contract and mark it trusted."), "{out}");
}

/// A marker that the gate cannot honour is refused, each at the line of the name it marks.
#[test]
fn gate_refuses_a_marker_it_cannot_honour() {
    require_clang_tidy();
    let f = fixture("markers-errors.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    for expected in [
        "markers-errors.cpp:5: marker: fast_sum is trusted and has no contract. Its callers rest on the contract alone.",
        "markers-errors.cpp:9: marker: no_reason has a marker with no reason. A trusted or plain marker gives its reason.",
        "markers-errors.cpp:12: marker: blank_reason has a marker with no reason. A trusted or plain marker gives its reason.",
        "markers-errors.cpp:19: marker: two_kinds has two kinds of marker. A function has one kind.",
        "markers-errors.cpp:23: marker: cplusp:trustd is no marker. The markers are in include/cplusp.h.",
        "markers-errors.cpp:25: marker: Box has a marker, and only a function or a plain type takes one.",
        "markers-errors.cpp:31: marker: cplusp:x y is no marker. The markers are in include/cplusp.h.",
        "markers-errors.cpp:34: marker: cplusp:assume waits until a case needs it. Mark the function trusted with a reason.",
        "markers-errors.cpp:38: marker: forged has a reason with a line break. A reason is one line.",
    ] {
        assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{expected}: {out}");
    }
    assert_eq!(out.lines().filter(|l| l.starts_with("Not provable: ")).count(), 9, "{out}");
}

/// Each function has its own kind, decision 0047. A local class, a lambda and an explicit specialization carry no marker of their own,
/// so they are verified inside a trusted body. A marked function whose first or last token is in a macro or another file is refused,
/// and its body is then verified. A function whose ends are in two files is refused whatever its kind, and code in a plain body is
/// plain, decision 0048. An abbreviated function template begins at its return type, decision 0049.
#[test]
fn a_finding_takes_the_kind_of_the_innermost_function_the_file_wrote() {
    require_clang_tidy();
    let f = fixture("markers-places.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [
        ("raw_allocation", 10),
        ("lambdas", 21),
        ("raw_allocation", 22),
        ("templates", 36),
        ("raw_allocation", 38),
        ("marker", 46),
        ("raw_allocation", 47),
        ("raw_allocation", 49),
        ("marker", 53),
        ("raw_allocation", 54),
        ("marker", 62),
    ]
    .into_iter()
    .map(|(r, n)| (r.to_string(), n))
    .collect();
    assert_eq!(reported, expected, "{out}");
    for name in ["ends_in_macro", "ends_elsewhere"] {
        let message = format!("marker: {name} starts or ends in a macro or in another file. Write its first and last token in its own file.");
        assert!(out.contains(&message), "{message}: {out}");
    }
}

/// Verified code runs no plain code, decision 0047. The gate reads the calls that run from the lowered form: a destructor that no call
/// names, an operator that the library calls, and a plain override that a call of its base can reach. A trusted body may run plain code.
/// A virtual call reaches every override in the module, one that a class template writes too, decision 0048.
#[test]
fn verified_code_runs_no_plain_code() {
    require_clang_tidy();
    let f = fixture("markers-reach.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [("marker", 17), ("marker", 29), ("marker", 41), ("marker", 47), ("marker", 75)].into_iter().map(|(r, n)| (r.to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
    for message in [
        "marker: verified code calls Guard::~Guard, which is plain. Give it a contract and mark it trusted.",
        "marker: verified code calls Key::operator<, which is plain. Give it a contract and mark it trusted.",
        "marker: Legacy::area is plain and overrides Shape::area, which is not plain. A verified call of Shape::area can run it.",
        "marker: verified code calls Legacy::area, which is plain. Give it a contract and mark it trusted.",
    ] {
        assert!(out.contains(message), "{message}: {out}");
    }
}

/// Each build is its own run, decision 0047. One build marks a header's body trusted and the other does not, so the finding of the
/// other stands.
#[test]
fn each_build_judges_its_own_findings() {
    require_clang_tidy();
    let (a, b) = (fixture("twice-a.cpp"), fixture("twice-b.cpp"));
    let o = gated(&[a.to_str().unwrap(), b.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let findings: Vec<&str> = out.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(findings.len(), 1, "{out}");
    assert!(findings[0].contains("twice.h:11: `new` / `delete`"), "{out}");
}

/// Each build is its own run, decision 0047, also when a compile database lists one file twice. The build with `-DLEGACY` marks the
/// header's body trusted, and the build without it does not, so the finding of the second build stands.
#[test]
fn each_entry_of_a_compile_database_is_its_own_run() {
    require_clang_tidy();
    let file = fixture("twice-b.cpp");
    let file = file.to_str().unwrap();
    let root = root();
    let dir = root.to_str().unwrap();
    let entries = [
        format!(r#"{{"directory": "{dir}", "arguments": ["clang++", "-std=c++23", "-ffp-contract=off", "-DLEGACY", "-c", "{file}"], "file": "{file}"}}"#),
        format!(r#"{{"directory": "{dir}", "arguments": ["clang++", "-std=c++23", "-ffp-contract=off", "-c", "{file}"], "file": "{file}"}}"#),
    ];
    let build = tempfile::tempdir().unwrap();
    std::fs::write(build.path().join("compile_commands.json"), format!("[{}]", entries.join(","))).unwrap();
    let o = gated(&["-p", build.path().to_str().unwrap(), file]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let findings: Vec<&str> = out.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(findings.len(), 1, "{out}");
    assert!(findings[0].contains("twice.h:11: `new` / `delete`"), "{out}");
}

/// An indirect call is named by constants alone, decision 0049. A pointer that a trusted call gives out, that a callable holds, or that a
/// trusted call stores in the caller's object has no name. So a call through it in verified code is a finding of `function_pointers`.
/// Only that row and the markers count here, because other rows judge the fields that hold the pointers.
#[test]
fn an_indirect_call_has_a_name_only_from_constants() {
    require_clang_tidy();
    let f = fixture("indirect-calls.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out
        .lines()
        .map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap()))
        .filter(|(r, _)| r == "function_pointers" || r == "marker")
        .collect();
    let expected: BTreeSet<(String, usize)> =
        [16, 27, 38, 67].into_iter().map(|n| ("function_pointers".to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
}

/// A type can be plain, decision 0051. Its fields, its static members and its member functions are out of view, and plain code may use
/// it. Verified code makes no object of it and reads no field of it. A call of a plain member is a call of plain code, decision 0047. A
/// reference to a plain type and a call of its trusted member are allowed.
#[test]
fn a_plain_type_is_out_of_view_and_verified_code_does_not_touch_it() {
    require_clang_tidy();
    let f = fixture("markers-types.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [29, 34, 39].into_iter().map(|n| ("marker".to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
    for message in [
        "marker: verified code uses Record, which is plain. Reach it through a trusted member.",
        "marker: verified code calls Record::twice, which is plain. Give it a contract and mark it trusted.",
    ] {
        assert!(out.contains(message), "{message}: {out}");
    }
}

/// A plain object goes only to the file's own code, decision 0052. A structured binding, a byte view through the library and a vector
/// of a plain type are uses. A member of a plain type that overrides a function that is not plain is refused. A verified member of a
/// plain type keeps its declaration in view, so the row `shared_ptr` sees its return type.
#[test]
fn a_plain_object_goes_only_to_the_files_own_code() {
    require_clang_tidy();
    let f = fixture("markers-types-reads.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [
        ("shared_ptr", 13),
        ("lvalue_references", 20),
        ("marker", 20),
        ("marker", 25),
        ("marker", 30),
        ("marker", 45),
    ]
    .into_iter()
    .map(|(r, n)| (r.to_string(), n))
    .collect();
    assert_eq!(reported, expected, "{out}");
    for message in [
        "marker: verified code uses Record, which is plain. Reach it through a trusted member.",
        "marker: Legacy::area is plain and overrides Shape::area, which is not plain. A verified call of Shape::area can run it.",
    ] {
        assert!(out.contains(message), "{message}: {out}");
    }
}

/// A pointer to a plain object counts as the object, and a friend defined in a plain type is plain, decision 0053. The library reads a
/// plain object through a pointer, and verified code calls a plain friend. A trusted friend keeps its contract, and the word `friend`
/// in a plain type is out of view.
#[test]
fn a_pointer_counts_as_the_object_and_a_friend_of_a_plain_type_is_plain() {
    require_clang_tidy();
    let f = fixture("markers-types-friends.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [("marker", 11), ("marker", 33)].into_iter().map(|(r, n)| (r.to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
    for message in [
        "marker: verified code uses Record, which is plain. Reach it through a trusted member.",
        "marker: verified code calls twice_of, which is plain. Give it a contract and mark it trusted.",
    ] {
        assert!(out.contains(message), "{message}: {out}");
    }
}

/// A cast of a pointer to a plain object into another pointer type is a use, decision 0054. Two casts through `const void*` hand the
/// bytes to the library, and an implicit cast hands them to a function of the file with a `const void*` parameter.
#[test]
fn a_cast_of_a_pointer_to_a_plain_object_is_a_use() {
    require_clang_tidy();
    let f = fixture("markers-types-casts.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [("marker", 17), ("marker", 26)].into_iter().map(|(r, n)| (r.to_string(), n)).collect();
    assert_eq!(reported, expected, "{out}");
    assert!(out.contains("marker: verified code uses Record, which is plain. Reach it through a trusted member."), "{out}");
}

/// The check of impure operators reads types, so it judges each instantiation, decision 0055. An operator whose parameter becomes a
/// pointer to non-const can write. A forwarding reference that becomes a const reference cannot. An operator in a template that
/// nothing instantiates is judged by its spelling, as before. Only that row counts here.
#[test]
fn the_impure_operator_check_judges_each_instantiation() {
    require_clang_tidy();
    let f = fixture("templates-impure.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let found: BTreeSet<usize> = out.lines().filter(|l| field(l, "rule") == "operator_overloading").map(|l| field(l, "line").parse::<usize>().unwrap()).collect();
    assert_eq!(found, BTreeSet::from([8, 35, 39]), "{out}");
}

//! One invariant over every case in divergence/dafny/cases: Dafny says what case.yaml says it says,
//! the gate and the witness show what case.yaml says they show, and the skill file carries the case's rule.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde::Deserialize;

#[derive(Deserialize)]
struct Case {
    construct: String,
    standard: String,
    row: String,
    #[allow(dead_code)]
    gap: u32,
    #[allow(dead_code)]
    cpp: String,
    #[allow(dead_code)]
    naive_does: String,
    side: Side,
    gate_rule: Option<String>,
    #[allow(dead_code)]
    mitigation: String,
    naive: Verdict,
    #[serde(default)]
    naive_is_wrong: bool,
    mitigated: Verdict,
    witness: Witness,
    rule: String,
}

/// What Dafny says about a file. `TypeError` is a file Dafny refuses before it verifies anything.
#[derive(Deserialize, PartialEq, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
enum Verdict {
    Verifies,
    Fails,
    TypeError,
}

/// Where the mitigation lives. See divergence/README.md.
#[derive(Deserialize, PartialEq, Debug, Clone, Copy)]
#[serde(rename_all = "lowercase")]
enum Side {
    Model,
    Contract,
    Cpp,
    Gate,
    None,
}

#[derive(Deserialize)]
struct Witness {
    #[allow(dead_code)]
    input: String,
    #[serde(default)]
    ubsan: bool,
    #[serde(default)]
    asan: bool,
    #[serde(default)]
    tsan: bool,
    prints: Option<String>,
    prints_gcc: Option<String>,
    fixed_prints: Option<String>,
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

fn dafny() -> String {
    if let Some(d) = std::env::var_os("DAFNY") {
        return d.to_string_lossy().into_owned();
    }
    if Path::new("/opt/dafny/dafny/dafny").exists() {
        return "/opt/dafny/dafny/dafny".into();
    }
    "dafny".into()
}

fn verdict(file: &Path) -> Verdict {
    let out = Command::new(dafny()).arg("verify").arg(file).output().expect("dafny runs");
    let text = String::from_utf8_lossy(&out.stdout) + String::from_utf8_lossy(&out.stderr);
    if text.contains("resolution/type errors detected") {
        return Verdict::TypeError;
    }
    assert!(text.contains("verifier finished"), "{}: dafny did not finish:\n{text}", file.display());
    if text.contains(", 0 errors") { Verdict::Verifies } else { Verdict::Fails }
}

/// UBSan, with float division by zero, which `undefined` leaves out.
const UBSAN: &[&str] = &["-fsanitize=undefined,float-divide-by-zero", "-fno-sanitize-recover=all"];
/// AddressSanitizer, with sized deallocation so a delete through the wrong type is caught.
const ASAN: &[&str] = &["-fsanitize=address", "-fsized-deallocation"];

fn build(compiler: &str, sources: &[&Path], exe: &Path, flags: &[&str]) -> Output {
    let mut c = Command::new(compiler);
    c.args(["-std=c++23", "-ffp-contract=off", "-O0"]).args(flags);
    c.args(sources).arg("-o").arg(exe).output().unwrap_or_else(|e| panic!("{compiler} runs: {e}"))
}

/// ThreadSanitizer, for a data race. It cannot run together with AddressSanitizer.
const TSAN: &[&str] = &["-fsanitize=thread", "-pthread"];

/// The sanitizers a case asks for, when it is built with clang.
fn sanitizers(asan: bool, tsan: bool) -> Vec<&'static str> {
    assert!(!(asan && tsan), "asan and tsan cannot run together");
    let mut flags = UBSAN.to_vec();
    if asan {
        flags.extend_from_slice(ASAN);
    }
    if tsan {
        flags.extend_from_slice(TSAN);
    }
    flags
}

fn run(exe: &Path) -> (String, String) {
    let o = Command::new(exe).output().expect("witness runs");
    (String::from_utf8_lossy(&o.stdout).into_owned(), String::from_utf8_lossy(&o.stderr).into_owned())
}

fn clang_tidy_available() -> bool {
    ["clang-tidy-18", "clang-tidy"].iter().any(|b| Command::new(b).arg("--version").output().map(|o| o.status.success()).unwrap_or(false))
}

/// The gate on one file, through the cplusp binary. The plugin must be built, as for the cli tests.
fn gate(file: &Path) -> Output {
    let plugin = std::env::var_os("CPLUSP_PLUGIN").map(PathBuf::from).unwrap_or_else(|| root().join("target/plugin/libcplusp.so"));
    assert!(plugin.exists(), "plugin not built: run `cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin`, or set CPLUSP_PLUGIN");
    Command::new("cargo")
        .args(["run", "-q", "-p", "cplusp", "--", "gate", "--json", "--plugin"])
        .arg(plugin)
        .arg(file)
        .args(["--", "-std=c++23", "-ffp-contract=off"])
        .current_dir(root())
        .output()
        .expect("cargo runs")
}

fn text(o: &Output) -> (String, String) {
    (String::from_utf8_lossy(&o.stdout).into_owned(), String::from_utf8_lossy(&o.stderr).into_owned())
}

#[test]
fn every_case_says_what_it_claims() {
    let cases = root().join("divergence/dafny/cases");
    let skill = std::fs::read_to_string(root().join("skills/cplusp-dafny/SKILL.md")).unwrap();
    let policy = std::fs::read_to_string(root().join("policy/cplusp-policy.yaml")).unwrap();
    let gate_available = clang_tidy_available();
    if !gate_available {
        eprintln!("skipped the gate: clang-tidy not installed");
    }
    let out_dir = std::env::temp_dir().join(format!("cplusp-divergence-{}", std::process::id()));
    std::fs::create_dir_all(&out_dir).unwrap();
    let check = |dir: &Path| {
        let id = dir.file_name().unwrap().to_string_lossy().into_owned();
        let case: Case = serde_yaml::from_str(&std::fs::read_to_string(dir.join("case.yaml")).unwrap()).unwrap_or_else(|e| panic!("{id}/case.yaml: {e}"));
        let code = dir.join("code.cpp");
        let witness = dir.join("witness.cpp");
        let fixed = dir.join("fixed.cpp");

        // The standard decides the case, and the case says where.
        assert!(case.standard.starts_with('[') && case.standard.contains("]: "), "{id}: standard is `[section]: the sentence that decides the case`, got: {}", case.standard);
        // The case exercises one row of the policy, which is how the battery covers the subset.
        assert!(policy.contains(&format!("- id: {}\n", case.row)), "{id}: row {} is not a row in the policy", case.row);

        // Dafny verdicts.
        assert_eq!(verdict(&dir.join("naive.dfy")), case.naive, "{id}: naive.dfy ({})", case.construct);
        assert_eq!(verdict(&dir.join("mitigated.dfy")), case.mitigated, "{id}: mitigated.dfy");
        assert_eq!(case.mitigated, Verdict::Verifies, "{id}: the mitigated model must verify, or it is not a mitigation");
        if case.naive_is_wrong {
            assert_eq!(case.naive, Verdict::Verifies, "{id}: a naive model can only be wrong if Dafny accepted it");
        }

        // The side says what else the case must carry.
        match case.side {
            Side::Gate => {
                let rule = case.gate_rule.as_deref().unwrap_or_else(|| panic!("{id}: a gate side names its gate_rule"));
                assert!(root().join("rules").join(rule).join("banned.cpp").exists(), "{id}: gate_rule {rule} has no sample pair under rules/");
                assert!(policy.contains(&format!("- id: {rule}\n")), "{id}: gate_rule {rule} is not a row in the policy");
            }
            _ => assert!(case.gate_rule.is_none(), "{id}: only a gate side names a gate_rule"),
        }
        let needs_fixed = matches!(case.side, Side::Cpp | Side::Gate);
        assert_eq!(fixed.exists(), needs_fixed, "{id}: fixed.cpp is the C++ changed under the rule, for a cpp or gate side only");

        // The witness, compiled with the sanitizer.
        let exe = out_dir.join(&id);
        let b = build("clang++-18", &[&code, &witness], &exe, &sanitizers(case.witness.asan, case.witness.tsan));
        assert!(b.status.success(), "{id}: witness does not build:\n{}", String::from_utf8_lossy(&b.stderr));
        let (out, err) = run(&exe);
        if case.witness.ubsan {
            assert!(err.contains("runtime error"), "{id}: the witness should hit undefined behaviour, stderr:\n{err}");
        } else {
            assert!(!err.contains("runtime error"), "{id}: unexpected undefined behaviour:\n{err}");
        }
        if case.witness.asan {
            assert!(err.contains("Sanitizer:"), "{id}: the witness should hit AddressSanitizer or LeakSanitizer, stderr:\n{err}");
        }
        if case.witness.tsan {
            assert!(err.contains("ThreadSanitizer:"), "{id}: the witness should hit ThreadSanitizer, stderr:\n{err}");
        }
        if let Some(expected) = &case.witness.prints {
            assert_eq!(out.trim(), expected.trim(), "{id}: witness output");
        }
        // Another compiler, where the standard leaves the result open.
        if let Some(expected) = &case.witness.prints_gcc {
            let exe = out_dir.join(format!("{id}-gcc"));
            let b = build("g++", &[&code, &witness], &exe, &[]);
            assert!(b.status.success(), "{id}: witness does not build with g++:\n{}", String::from_utf8_lossy(&b.stderr));
            let (out, _) = run(&exe);
            assert_eq!(out.trim(), expected.trim(), "{id}: witness output under g++");
        }

        // The C++ under the rule: no undefined behaviour, and the same output under both compilers.
        if needs_fixed {
            let expected = case.witness.fixed_prints.as_deref().unwrap_or_else(|| panic!("{id}: fixed.cpp needs witness.fixed_prints"));
            for (compiler, flags) in [("clang++-18", sanitizers(case.witness.asan, case.witness.tsan)), ("g++", Vec::new())] {
                let exe = out_dir.join(format!("{id}-fixed-{compiler}"));
                let b = build(compiler, &[&fixed, &witness], &exe, &flags);
                assert!(b.status.success(), "{id}: fixed.cpp does not build with {compiler}:\n{}", String::from_utf8_lossy(&b.stderr));
                let (out, err) = run(&exe);
                assert!(!err.contains("runtime error") && !err.contains("Sanitizer:"), "{id}: fixed.cpp hits a sanitizer:\n{err}");
                assert_eq!(out.trim(), expected.trim(), "{id}: fixed.cpp output under {compiler}");
            }
        }

        // The gate: the case is about C+P code, so code.cpp passes, unless the gate row is the mitigation.
        if gate_available {
            let o = gate(&code);
            let (out, err) = text(&o);
            match (&case.side, &case.gate_rule) {
                (Side::Gate, Some(rule)) => {
                    assert_eq!(o.status.code(), Some(1), "{id}: code.cpp must fail the gate, that is the mitigation. stdout: {out} stderr: {err}");
                    for line in out.lines() {
                        assert!(line.contains(&format!("\"rule\":\"{rule}\"")), "{id}: the gate must report code.cpp under {rule}, got: {line}");
                    }
                }
                _ => assert!(o.status.code() == Some(0) && out.trim().is_empty(), "{id}: code.cpp must pass the gate, or the case is not about C+P. stdout: {out} stderr: {err}"),
            }
            if needs_fixed {
                let o = gate(&fixed);
                let (out, err) = text(&o);
                assert!(o.status.code() == Some(0) && out.trim().is_empty(), "{id}: fixed.cpp must pass the gate. stdout: {out} stderr: {err}");
            }
        }

        // The rule is in the skill, word for word.
        assert!(skill.contains(&format!("## {id}")), "{id}: no section in skills/cplusp-dafny/SKILL.md");
        for line in case.rule.lines().filter(|l| !l.trim().is_empty()) {
            assert!(skill.contains(line.trim()), "{id}: rule line missing from the skill: {line}");
        }
    };
    // Dafny takes a second per file, so the cases run on a few threads. A panic in any of them fails the test.
    let dirs: Vec<PathBuf> = std::fs::read_dir(&cases).unwrap().map(|e| e.unwrap().path()).filter(|d| d.is_dir()).collect();
    assert!(!dirs.is_empty(), "no cases found");
    let per_thread = dirs.len().div_ceil(4);
    std::thread::scope(|s| {
        for chunk in dirs.chunks(per_thread) {
            let check = &check;
            s.spawn(move || chunk.iter().for_each(|d| check(d)));
        }
    });
    let _ = std::fs::remove_dir_all(&out_dir);
}

/// docs/mitigations-dafny.md is generated from the cases. It must match what the generator says today.
#[test]
fn the_mitigation_report_is_up_to_date() {
    let o = Command::new(env!("CARGO_BIN_EXE_divergence")).arg("dafny").current_dir(root()).output().expect("divergence runs");
    assert!(o.status.success(), "stderr: {}", String::from_utf8_lossy(&o.stderr));
    let expected = String::from_utf8_lossy(&o.stdout).into_owned();
    let actual = std::fs::read_to_string(root().join("docs/mitigations-dafny.md")).expect("docs/mitigations-dafny.md exists");
    assert_eq!(actual, expected, "docs/mitigations-dafny.md is stale. Run: cargo run -p divergence -- dafny > docs/mitigations-dafny.md");
}

/// The shape of the report, pinned so the docs reader can rely on it.
#[test]
fn the_mitigation_report_has_one_row_per_case_in_a_fixed_shape() {
    let report = divergence::report(&root().join("divergence/dafny")).expect("report");
    let mut lines = report.lines();
    assert_eq!(lines.next().unwrap(), "# Mitigations: dafny");
    assert!(report.contains("Generated by `cargo run -p divergence -- dafny` from `divergence/dafny/cases/*/case.yaml`. Do not edit by hand."), "{report}");
    assert!(report.contains("The fields are explained in divergence/README.md."), "{report}");
    assert!(report.contains("| Case | Construct | Standard | Gap | C++ does | Naive model does | Naive verdict | Mitigation | Side |"), "{report}");
    assert!(report.contains("| signed_overflow | Signed addition on int32_t | [expr.pre]: "), "{report}");
    assert!(report.contains("| verifies, wrong |"), "{report}");
    assert!(report.contains("| type_error |"), "{report}");
    assert!(report.contains("| contract |"), "{report}");
    let cases = std::fs::read_dir(root().join("divergence/dafny/cases")).unwrap().filter(|e| e.as_ref().unwrap().path().is_dir()).count();
    let rows = report.lines().filter(|l| l.starts_with("| ") && !l.starts_with("| Case") && !l.starts_with("| ---")).count();
    assert_eq!(rows, cases, "one row per case");
}

/// A prover directory with one case, for the generator's own checks.
fn scratch_prover(name: &str, id: &str, yaml: Option<&str>) -> PathBuf {
    let prover = std::env::temp_dir().join(format!("cplusp-report-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&prover);
    std::fs::create_dir_all(prover.join("cases").join(id)).unwrap();
    if let Some(yaml) = yaml {
        std::fs::write(prover.join("cases").join(id).join("case.yaml"), yaml).unwrap();
    }
    prover
}

const A_CASE: &str = "construct: X\nstandard: \"[x]: y.\"\nrow: arithmetic\ngap: 3\ncpp: a\nnaive_does: b\nmitigation: c\n";

/// The generator checks what it prints, so a wrong case.yaml cannot become a wrong row.
#[test]
fn the_report_refuses_a_case_it_cannot_print_right() {
    let wrong_flag = scratch_prover("flag", "x", Some(&format!("{A_CASE}naive: fails\nnaive_is_wrong: true\nmitigated: verifies\nside: model\n")));
    let err = divergence::report(&wrong_flag).expect_err("a naive model that fails cannot be wrong").to_string();
    assert!(err.contains("x/case.yaml") && err.contains("naive_is_wrong needs naive: verifies"), "{err}");

    let bad_side = scratch_prover("side", "x", Some(&format!("{A_CASE}naive: verifies\nmitigated: verifies\nside: sideways\n")));
    let err = divergence::report(&bad_side).expect_err("an unknown side").to_string();
    assert!(err.contains("x/case.yaml") && err.contains("side"), "{err}");

    let bad_verdict = scratch_prover("verdict", "x", Some(&format!("{A_CASE}naive: verifys\nmitigated: verifies\nside: model\n")));
    let err = divergence::report(&bad_verdict).expect_err("an unknown verdict").to_string();
    assert!(err.contains("x/case.yaml") && err.contains("naive"), "{err}");

    let no_yaml = scratch_prover("missing", "empty", None);
    let err = divergence::report(&no_yaml).expect_err("a folder without case.yaml").to_string();
    assert!(err.contains("empty/case.yaml"), "{err}");
}

/// The rows a case may claim: the policy's rules, with their decisions.
#[derive(Deserialize)]
struct PolicyRows {
    rules: Vec<PolicyRow>,
}

#[derive(Deserialize)]
struct PolicyRow {
    id: String,
    decision: String,
}

#[derive(Deserialize)]
struct CaseRow {
    row: String,
}

/// Every feature C+P supports has a case: each row the policy allows or restricts is the `row` of at least
/// one case. The list of rows without a case shrinks with every round of the battery, to empty.
#[test]
fn every_supported_row_has_a_case() {
    const NOT_YET: &[&str] = &[];
    let policy: PolicyRows = serde_yaml::from_str(&std::fs::read_to_string(root().join("policy/cplusp-policy.yaml")).unwrap()).unwrap();
    let mut covered = std::collections::BTreeSet::new();
    for entry in std::fs::read_dir(root().join("divergence/dafny/cases")).unwrap() {
        let dir = entry.unwrap().path();
        if dir.is_dir() {
            let case: CaseRow = serde_yaml::from_str(&std::fs::read_to_string(dir.join("case.yaml")).unwrap()).unwrap();
            covered.insert(case.row);
        }
    }
    for rule in policy.rules.iter().filter(|r| r.decision == "allow" || r.decision == "restrict") {
        if NOT_YET.contains(&rule.id.as_str()) {
            assert!(!covered.contains(&rule.id), "{}: now has a case, take it off NOT_YET", rule.id);
        } else {
            assert!(covered.contains(&rule.id), "{}: a row the policy allows has no case in the battery", rule.id);
        }
    }
}

/// Every row the bot may use has an example under examples/: the C++ under the row, which passes the gate,
/// and the Dafny the bot writes for it, which verifies. A trusted_only row also has the trusted body, which the
/// gate refuses under that row, so the construct is really there. See examples/README.md.
#[test]
fn every_row_the_bot_may_use_has_an_example() {
    let policy: PolicyRows = serde_yaml::from_str(&std::fs::read_to_string(root().join("policy/cplusp-policy.yaml")).unwrap()).unwrap();
    let rows: Vec<&PolicyRow> = policy.rules.iter().filter(|r| r.decision != "ban").collect();
    let gate_available = clang_tidy_available();
    let check = |row: &PolicyRow| {
        let dir = root().join("examples").join(&row.id);
        let id = &row.id;
        assert!(dir.is_dir(), "{id}: a row the bot may use has no example under examples/");
        let (cpp, dfy, trusted) = (dir.join("example.cpp"), dir.join("example.dfy"), dir.join("trusted.cpp"));
        assert!(cpp.exists() && dfy.exists(), "{id}: an example needs example.cpp and example.dfy");
        assert_eq!(trusted.exists(), row.decision == "trusted_only", "{id}: trusted.cpp is for a trusted_only row only, and every such row has one");
        if trusted.exists() {
            let declaration = std::fs::read_to_string(&cpp).unwrap();
            assert!(declaration.contains("CPLUSP_TRUSTED(\""), "{id}: the trusted declaration in example.cpp carries CPLUSP_TRUSTED with a reason, from include/cplusp.h");
        }
        assert_eq!(verdict(&dfy), Verdict::Verifies, "{id}: example.dfy must verify");
        if gate_available {
            let o = gate(&cpp);
            let (out, err) = text(&o);
            assert!(o.status.code() == Some(0) && out.trim().is_empty(), "{id}: example.cpp must pass the gate. stdout: {out} stderr: {err}");
            if trusted.exists() {
                let o = gate(&trusted);
                let (out, err) = text(&o);
                assert_eq!(o.status.code(), Some(1), "{id}: trusted.cpp must fail the gate, it holds the construct. stdout: {out} stderr: {err}");
                for line in out.lines() {
                    assert!(line.contains(&format!("\"rule\":\"{id}\"")), "{id}: the gate must refuse trusted.cpp under {id} only, got: {line}");
                }
            }
        }
    };
    std::thread::scope(|s| {
        let mut rest = rows.as_slice();
        let mut handles = Vec::new();
        for _ in 0..4 {
            let (mine, others) = rest.split_at(rest.len().div_ceil(4).min(rest.len()));
            rest = others;
            handles.push(s.spawn(move || mine.iter().for_each(|r| check(r))));
        }
        for h in handles {
            h.join().unwrap();
        }
    });
}

/// The cases each round of the battery planned. A missing one is work not done.
#[test]
fn the_battery_has_the_planned_cases() {
    let cases = root().join("divergence/dafny/cases");
    for id in [
        // Round one: arithmetic and control.
        "signed_overflow", "unsigned_wrap", "integral_promotion", "signed_division", "narrowing_cast", "shift", "sign_compare",
        "plain_int", "reference_aliasing", "evaluation_order", "loop_underflow", "index_out_of_range", "optional_deref", "bool_from_int",
        // Round C1: arithmetic and conversions.
        "promotion_before_widening", "implicit_narrowing", "compound_assign_narrow", "signed_to_unsigned", "unary_minus_min", "abs_min",
        "increment_overflow", "signed_shift_left", "signed_shift_right", "literal_shift", "bool_arith", "enum_cast", "size_minus_one",
        // Round C2: objects and memory.
        "value_semantics", "object_lifetime", "reference_into_container", "member_init_order", "slicing", "virtual_in_constructor",
        "virtual_destructor", "use_after_move", "moved_from_unique_ptr", "null_pointer", "operator_meaning", "generic_per_type",
        "stack_depth", "constexpr_runtime", "interface_dispatch",
        // Round C3: library and control.
        "array_index", "span_dangling", "range_for_mutation", "count_if_lambda", "fold_init_type", "sort_contract", "map_subscript",
        "string_npos", "switch_fallthrough", "switch_missing_case", "optional_compare", "variant_get",
        // Round C4: floating point as a real after rounding, and a pointer into a container.
        "double_sum", "double_nan", "double_to_int", "double_cancellation", "double_increment", "double_division_zero", "int_to_double",
        "pointer_into_container",
        // The float review: a product that underflows. The last round: state.
        "double_underflow", "unlisted_modifies", "static_local", "global_constructors", "torn_read", "single_precision", "double_literal",
    ] {
        assert!(cases.join(id).join("case.yaml").exists(), "no case {id}");
    }
}

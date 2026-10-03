//! The command as the bot and a human run it. docs/policy.md is the reference.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn cplusp(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cplusp"))
        .args(args)
        .current_dir(root())
        .output()
        .expect("cplusp runs")
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// The clang-tidy plugin, built by `cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin`.
fn plugin() -> PathBuf {
    let p = std::env::var_os("CPLUSP_PLUGIN").map(PathBuf::from).unwrap_or_else(|| root().join("target/plugin/libcplusp.so"));
    assert!(p.exists(), "plugin not built: run `cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin`, or set CPLUSP_PLUGIN");
    p
}

fn clang_tidy_available() -> bool {
    ["clang-tidy-18", "clang-tidy"]
        .iter()
        .any(|b| Command::new(b).arg("--version").output().map(|o| o.status.success()).unwrap_or(false))
}

// ------------------------------------------------------------------ policy

#[test]
fn policy_check_accepts_the_default_policy() {
    let o = cplusp(&["policy", "check"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    assert!(stdout(&o).starts_with("ok: "), "stdout: {}", stdout(&o));
}

#[test]
fn policy_check_names_every_problem_in_a_broken_policy() {
    let f = fixture("broken.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    assert!(err.contains("iterators: restrict needs a limit"), "{err}");
    assert!(err.contains("goto: ban needs detect"), "{err}");
    assert!(err.contains("unions: check misspelt-check is not known"), "{err}");
}

#[test]
fn policy_emit_is_the_clang_tidy_config_for_the_default_policy() {
    let o = cplusp(&["policy", "emit"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    assert!(out.contains("Checks:"), "{out}");
    assert!(out.contains("-*"), "{out}");
    assert!(out.contains("google-readability-casting"), "{out}");
    assert!(out.contains("cppcoreguidelines-avoid-goto"), "{out}");
    assert!(out.contains("WarningsAsErrors: '*'"), "{out}");
    assert!(out.contains("cplusp-multiple-inheritance.AllowPureInterfaces: 'true'"), "{out}");
    // A dormant check on an allow row never reaches the config.
    assert!(!out.contains("cppcoreguidelines-pro-bounds-constant-array-index"), "{out}");
    // Every check once.
    assert_eq!(out.matches("google-readability-casting").count(), 1, "{out}");
}

#[test]
fn policy_show_prints_one_row_per_rule_with_its_limit() {
    let o = cplusp(&["policy", "show"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    let casts = out.lines().find(|l| l.contains("c_style_casts")).expect("row for c_style_casts");
    assert!(casts.contains("ban"), "{casts}");
    let iter = out.lines().find(|l| l.contains("iterators")).expect("row for iterators");
    assert!(iter.contains("restrict") && iter.contains("Range-for only."), "{iter}");
    let floats = out.lines().find(|l| l.contains("floating_point")).expect("row for floating_point");
    assert!(floats.contains("prover"), "{floats}");
}

#[test]
fn policy_doc_prints_the_markdown_table_from_the_plan() {
    let o = cplusp(&["policy", "doc"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    let mut lines = out.lines();
    assert_eq!(lines.next().unwrap(), "| Area | Construct | Canonical stance | Why, for us | Decision | Stage |");
    assert_eq!(lines.next().unwrap(), "| --- | --- | --- | --- | --- | --- |");
    assert!(out.contains("| Control | `goto` | MISRA ban | No benefit. | Ban | Gate |"), "{out}");
}

// --------------------------------------------------------------- overrides

#[test]
fn a_team_policy_may_tighten_without_a_reason() {
    let f = fixture("team-tighten.yaml");
    let o = cplusp(&["policy", "emit", "--policy", f.to_str().unwrap()]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    assert!(stdout(&o).contains("cppcoreguidelines-pro-bounds-constant-array-index"), "{}", stdout(&o));
}

#[test]
fn a_team_policy_that_loosens_without_a_reason_is_refused() {
    let f = fixture("team-loosen-bad.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2));
    assert!(stderr(&o).contains("goto: loosened without loosened_because"), "{}", stderr(&o));
}

#[test]
fn a_team_policy_that_loosens_with_a_reason_is_reported_first() {
    let f = fixture("team-loosen.yaml");
    let o = cplusp(&["policy", "emit", "--policy", f.to_str().unwrap()]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let first = stderr(&o).lines().next().unwrap_or("").to_string();
    assert_eq!(first, "loosened: goto. Legacy parser uses goto for its state machine.");
    assert!(!stdout(&o).contains("cppcoreguidelines-avoid-goto"), "{}", stdout(&o));
}

// -------------------------------------------------------------------- gate

#[test]
fn gate_passes_an_allowed_sample_and_fails_a_banned_one() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let allowed = root().join("rules/c_style_casts/allowed.cpp");
    let o = cplusp(&["gate", allowed.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stdout(&o).trim(), "ok: no findings");

    let banned = root().join("rules/c_style_casts/banned.cpp");
    let o = cplusp(&["gate", banned.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    let expected = "banned.cpp:4: C-style casts: not allowed in verified code. Hides what kind of cast it is. All forms, including plain numeric narrowing. Use static_cast, or std::bit_cast for a byte view.";
    assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{out}");
}

#[test]
fn gate_reports_a_trusted_only_construct_with_its_own_wording() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let banned = root().join("rules/reinterpret_const_cast/banned.cpp");
    let o = cplusp(&["gate", banned.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    let expected = "banned.cpp:4: `reinterpret_cast`, `const_cast`: allowed only in trusted code. Defeats the type model. Most forms are UB. Use std::bit_cast, or mark the function trusted with a reason.";
    assert!(out.lines().any(|l| l.ends_with(expected)), "{out}");
}

#[test]
fn gate_refuses_a_file_that_does_not_compile() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let f = fixture("does-not-compile.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stdout(&o).trim(), "", "nothing on stdout for a file that does not compile");
    let err = stderr(&o);
    assert!(err.lines().any(|l| l.starts_with("does not compile: ") && l.contains("does-not-compile.cpp:1:")), "{err}");
}

#[test]
fn gate_refuses_a_compile_error_named_after_a_warning() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("narrowing.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).lines().any(|l| l.starts_with("does not compile: ") && l.contains("narrowing.cpp:1:")), "{}", stderr(&o));
}

#[test]
fn gate_treats_nolint_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("nolint.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let expected = "nolint.cpp:3: NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.";
    assert!(stdout(&o).lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{}", stdout(&o));
}

#[test]
fn gate_refuses_a_build_dir_without_compile_commands() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "-p", root().to_str().unwrap(), f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("compile_commands.json"), "{}", stderr(&o));
}

#[test]
fn gate_refuses_a_build_dir_together_with_trailing_flags() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "-p", root().to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("Use -p or --, not both."), "{}", stderr(&o));
}

#[test]
fn gate_names_the_checks_that_do_not_exist_yet() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    let line = err.lines().find(|l| l.starts_with("warning: not enforced, no such check: ")).expect(&err);
    assert!(line.contains("cplusp-matcher"), "{line}");
    assert!(!line.contains("cppcoreguidelines-avoid-goto"), "{line}");
}

#[test]
fn gate_with_the_plugin_no_longer_warns_about_the_generic_check() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "--plugin", plugin().to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    for line in err.lines().filter(|l| l.starts_with("warning: not enforced")) {
        assert!(!line.contains("cplusp-matcher"), "{line}");
    }
}

#[test]
fn policy_emit_turns_matcher_patterns_into_options_of_the_generic_check() {
    let o = cplusp(&["policy", "emit"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    let checks = out.lines().find(|l| l.starts_with("Checks:")).expect("Checks line");
    assert_eq!(checks.matches("cplusp-matcher").count(), 1, "{checks}");
    assert!(out.contains("  cplusp-matcher.unscoped_enum/1: 'enumDecl(unless(isScoped()), unless(isImplicit()))'"), "{out}");
    assert!(out.contains("  cplusp-matcher.exceptions/1: 'cxxThrowExpr()'"), "{out}");
    assert!(out.contains("  cplusp-matcher.exceptions/2: 'cxxTryStmt()'"), "{out}");
}

#[test]
fn gate_refuses_a_policy_whose_matcher_does_not_parse() {
    if !clang_tidy_available() {
        return;
    }
    let policy = fixture("bad-matcher.yaml");
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "--plugin", plugin().to_str().unwrap(), "--policy", policy.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    assert!(err.contains("bad_rule") && err.contains("matcher"), "{err}");
    assert_eq!(stdout(&o).trim(), "", "nothing on stdout for a broken policy");
}

#[test]
fn policy_emit_judges_project_headers_too() {
    let o = cplusp(&["policy", "emit"]);
    assert!(stdout(&o).contains("HeaderFilterRegex: '.*'"), "{}", stdout(&o));
}

#[test]
fn a_team_policy_with_a_misspelt_rules_key_is_refused() {
    let f = fixture("team-misspelt.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("rules"), "{}", stderr(&o));
}

#[test]
fn an_override_with_a_field_it_may_not_set_is_refused() {
    let f = fixture("team-unknown-key.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("detect"), "{}", stderr(&o));
}

#[test]
fn gate_prints_each_finding_once() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("twice.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let lines: Vec<&str> = stdout(&o).lines().map(|l| l.trim()).filter(|l| !l.is_empty()).collect::<Vec<_>>().into_iter().map(|l| Box::leak(l.to_string().into_boxed_str()) as &str).collect();
    let distinct: BTreeSet<&str> = lines.iter().copied().collect();
    assert_eq!(lines.len(), distinct.len(), "duplicate lines: {:?}", lines);
    assert!(lines.iter().any(|l| l.contains("twice.cpp:3:")), "{:?}", lines);
}

#[test]
fn gate_prints_paths_relative_to_the_working_directory() {
    if !clang_tidy_available() {
        return;
    }
    let o = cplusp(&["gate", "rules/goto/banned.cpp", "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.starts_with("Not provable: rules/goto/banned.cpp:4: ")), "{}", stdout(&o));
}

#[test]
fn gate_names_a_missing_input_file() {
    if !clang_tidy_available() {
        return;
    }
    let o = cplusp(&["gate", "nope.cpp", "--", "-std=c++20"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("cannot read nope.cpp"), "{}", stderr(&o));
}

#[test]
fn policy_show_marks_a_loosened_rule() {
    let f = fixture("team-loosen.yaml");
    let o = cplusp(&["policy", "show", "--policy", f.to_str().unwrap()]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let row = stdout(&o).lines().find(|l| l.contains("goto")).expect("row for goto").to_string();
    assert!(row.contains("allow") && row.contains("loosened"), "{row}");
}

/// The invariant behind every sample pair: `allowed.cpp` is clean, and `banned.cpp`
/// is reported on exactly the lines marked `// BANNED`, each by its own rule.
#[test]
fn every_sample_pair_agrees_with_its_rule() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let rules_dir = root().join("rules");
    let mut checked = 0;
    for entry in std::fs::read_dir(&rules_dir).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        let id = dir.file_name().unwrap().to_str().unwrap().to_string();
        let allowed = dir.join("allowed.cpp");
        let banned = dir.join("banned.cpp");
        assert!(allowed.exists() && banned.exists(), "rule {id} needs allowed.cpp and banned.cpp");

        let plugin = plugin();
        let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), allowed.to_str().unwrap(), "--", "-std=c++20"]);
        assert_eq!(o.status.code(), Some(0), "{id}/allowed.cpp: stdout {} stderr {}", stdout(&o), stderr(&o));
        assert_eq!(stdout(&o).trim(), "", "{id}/allowed.cpp must produce no findings");

        let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), banned.to_str().unwrap(), "--", "-std=c++20"]);
        assert_eq!(o.status.code(), Some(1), "{id}/banned.cpp: stdout {} stderr {}", stdout(&o), stderr(&o));
        let reported: BTreeSet<(String, usize)> = stdout(&o)
            .lines()
            .map(|l| {
                let rule = field(l, "rule");
                let line = field(l, "line").parse::<usize>().unwrap();
                (rule, line)
            })
            .collect();
        let expected: BTreeSet<(String, usize)> = std::fs::read_to_string(&banned)
            .unwrap()
            .lines()
            .enumerate()
            .filter(|(_, l)| l.contains("// BANNED"))
            .map(|(i, _)| (id.clone(), i + 1))
            .collect();
        assert_eq!(reported, expected, "{id}/banned.cpp");
        checked += 1;
    }
    // Every rule the gate enforces today has a pair: the 8 upstream ones and the 18 matcher ones.
    for id in [
        "unscoped_enum", "unions", "bitfields", "virtual_inheritance", "exceptions", "shared_ptr", "implicit_conversions",
        "function_pointers", "varargs_coroutines", "concurrency", "volatile", "inline_asm_intrinsics", "unreachable_assume",
        "longjmp", "raw_memory_ops", "launder_placement_new", "templates", "metaprogramming",
    ] {
        assert!(rules_dir.join(id).is_dir(), "no sample pair for matcher rule {id}");
    }
    assert!(checked >= 26, "expected at least 26 sample pairs, found {checked}");
}

/// Pull `"key":"value"` or `"key":123` out of one JSON line without a JSON library.
fn field(line: &str, key: &str) -> String {
    let needle = format!("\"{key}\":");
    let start = line.find(&needle).expect(key) + needle.len();
    let rest = &line[start..];
    if let Some(r) = rest.strip_prefix('"') {
        r[..r.find('"').unwrap()].to_string()
    } else {
        rest.chars().take_while(|c| c.is_ascii_digit()).collect()
    }
}

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
/// The gate with the plugin, which is the only run the gate accepts as complete.
fn gated(args: &[&str]) -> Output {
    let plugin = plugin();
    let mut full = vec!["gate", "--plugin", plugin.to_str().unwrap()];
    full.extend(args.iter().copied());
    cplusp(&full)
}

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
    assert!(out.contains("cppcoreguidelines-init-variables"), "{out}");
    assert!(out.contains("cplusp-allowlist"), "{out}");
    assert!(out.contains("WarningsAsErrors: '*'"), "{out}");
    // A dormant check on an allow row never reaches the config.
    assert!(!out.contains("cppcoreguidelines-pro-bounds-constant-array-index"), "{out}");
    // Every check once, though many rows name it.
    let checks = out.lines().find(|l| l.starts_with("Checks:")).expect("Checks line");
    assert_eq!(checks.matches("cplusp-allowlist").count(), 1, "{checks}");
    assert_eq!(checks.matches("cppcoreguidelines-init-variables").count(), 1, "{checks}");
}

/// A `clang-diagnostic-{name}` check reports only when the compiler has `-W{name}` on, and clang leaves
/// some of them off. The config turns on every one the policy names.
#[test]
fn policy_emit_turns_on_the_warning_of_every_diagnostic_check() {
    let o = cplusp(&["policy", "emit"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    assert!(out.contains("\nExtraArgs: ['-Wreturn-stack-address', '-Wreorder-ctor', '-Wimplicit-fallthrough', '-Wswitch', '-Wunsequenced', '-Wglobal-constructors']\n"), "{out}");
}

/// A diagnostic name is a compiler flag once it is in the config. Three names must never get there:
/// `clang-diagnostic-error` would turn a compile error into a finding, `clang-diagnostic-no-...` would switch a
/// warning off, and a quote would break the YAML with clang-tidy's message instead of the gate's.
/// Decision 0025 retired the two checks that were never built. A policy that names one is refused like any unknown check.
#[test]
fn policy_check_refuses_a_retired_check() {
    let f = fixture("retired-check.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("retired: check cplusp-recursion is not known"), "{}", stderr(&o));
}

#[test]
fn policy_check_refuses_a_diagnostic_name_that_is_not_a_warning() {
    let f = fixture("evil-check.yaml");
    let o = cplusp(&["policy", "check", "--policy", f.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    assert!(err.contains("evil_error: check clang-diagnostic-error is not known"), "{err}");
    assert!(err.contains("evil_no: check clang-diagnostic-no-unused is not known"), "{err}");
    assert!(err.contains("evil_quote: check clang-diagnostic-foo'bar is not known"), "{err}");
}

/// The subset table in docs/plan.md is generated. It must be what the generator prints today.
#[test]
fn the_plan_carries_the_current_subset_table() {
    let o = cplusp(&["policy", "doc"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let doc = stdout(&o);
    let generated: Vec<&str> = doc.lines().filter(|l| l.starts_with("| ")).collect();
    let plan = std::fs::read_to_string(root().join("docs/plan.md")).unwrap();
    let start = plan.find("Generated by `cplusp policy doc`").expect("the marker line in docs/plan.md");
    let in_plan: Vec<&str> = plan[start..].lines().skip_while(|l| !l.starts_with("| ")).take_while(|l| l.starts_with("| ")).collect();
    assert_eq!(in_plan, generated, "docs/plan.md's subset table is stale. Paste the table from `cplusp policy doc` under its marker line.");
}

#[test]
fn policy_emit_carries_a_check_option_into_the_config() {
    let f = fixture("with-option.yaml");
    let o = cplusp(&["policy", "emit", "--policy", f.to_str().unwrap()]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    assert!(stdout(&o).contains("CheckOptions:\n  google-readability-casting.WarnOnNarrowing: 'true'"), "{}", stdout(&o));
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
    let doubles = out.lines().find(|l| l.split_whitespace().nth(1) == Some("double")).expect("row for double");
    assert!(doubles.contains("prover"), "{doubles}");
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
    let o = gated(&[allowed.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stdout(&o).trim(), "ok: no findings");

    let banned = root().join("rules/c_style_casts/banned.cpp");
    let o = gated(&[banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    let expected = "banned.cpp:4: C-style casts: not allowed in verified code. Hides what kind of cast it is. All forms, including plain numeric narrowing. Use static_cast, or std::bit_cast for a byte view. The construct is CStyleCastExpr.";
    assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{out}");
}

#[test]
fn gate_reports_a_trusted_only_construct_with_its_own_wording() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let banned = root().join("rules/reinterpret_const_cast/banned.cpp");
    let o = gated(&[banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    let expected = "banned.cpp:4: `reinterpret_cast`, `const_cast`: allowed only in trusted code. Defeats the type model. Most forms are UB. Use std::bit_cast, or mark the function trusted with a reason. The construct is CXXReinterpretCastExpr.";
    assert!(out.lines().any(|l| l.ends_with(expected)), "{out}");
}

#[test]
fn gate_refuses_a_file_that_does_not_compile() {
    if !clang_tidy_available() {
        eprintln!("skipped: clang-tidy not installed");
        return;
    }
    let f = fixture("does-not-compile.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
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
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).lines().any(|l| l.starts_with("does not compile: ") && l.contains("narrowing.cpp:1:")), "{}", stderr(&o));
}

#[test]
fn gate_treats_nolint_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("nolint.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let expected = "nolint.cpp:3: NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.";
    assert!(stdout(&o).lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{}", stdout(&o));
}

/// The proofs assume C++23, IEEE 754 arithmetic as written, and the compiler warnings the policy names.
/// The flags after `--` can break all three, so the gate reads them before clang-tidy does.
#[test]
fn gate_refuses_flags_the_proofs_cannot_follow() {
    if !clang_tidy_available() {
        return;
    }
    let float = "not allowed with the gate. It changes floating-point results, and the proofs assume IEEE 754 round to nearest.";
    for (flags, message) in [
        (vec!["-std=c++23", "-ffp-contract=off", "-ffast-math"], format!("-ffast-math: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-Ofast"], format!("-Ofast: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-contract=fast"], format!("-ffp-contract=fast: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffinite-math-only"], format!("-ffinite-math-only: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-model=fast"], format!("-ffp-model=fast: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-fdenormal-fp-math=preserve-sign"], format!("-fdenormal-fp-math=preserve-sign: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-mfpmath=387"], format!("-mfpmath=387: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-m32"], format!("-m32: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-contract=on"], format!("-ffp-contract=on: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-model=precise"], format!("-ffp-model=precise: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-eval-method=extended"], format!("-ffp-eval-method=extended: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-ffp-eval-method=double"], format!("-ffp-eval-method=double: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "--std=c++17"], "--std=c++17: not allowed with the gate. The proofs assume C++23 or later.".to_string()),
        (vec!["-std=c++20", "-ffp-contract=off"], "-std=c++20: not allowed with the gate. The proofs assume C++23 or later.".to_string()),
        (vec!["-ffp-contract=off"], "no -std flag: the gate needs -std=c++23 or later, because the proofs assume C++23.".to_string()),
        (vec!["-std=c++23"], "no -ffp-contract=off: the gate needs it, because the proofs assume no fused multiply-add.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-w"], "-w: not allowed with the gate. It hides the compiler warnings the policy names.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-Wno-everything"], "-Wno-everything: not allowed with the gate. It hides the compiler warnings the policy names.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-Wno-unsequenced"], "-Wno-unsequenced: not allowed with the gate. It hides a compiler warning the policy names.".to_string()),
    ] {
        let mut args = vec!["rules/goto/allowed.cpp", "--"];
        args.extend(flags.iter().copied());
        let o = gated(&args);
        assert_eq!(o.status.code(), Some(2), "{flags:?}: stdout {} stderr {}", stdout(&o), stderr(&o));
        assert_eq!(stdout(&o).trim(), "", "{flags:?}: nothing on stdout for a refused build");
        assert!(stderr(&o).lines().any(|l| l == message), "{flags:?}: stderr {}", stderr(&o));
    }
    for std in ["-std=c++23", "-std=c++2b", "-std=c++26", "-std=gnu++23"] {
        let o = gated(&["rules/goto/allowed.cpp", "--", std, "-ffp-contract=off", "-fdenormal-fp-math=ieee", "-ffp-model=strict", "-ffp-eval-method=source", "-Wno-unused-variable"]);
        assert_eq!(o.status.code(), Some(0), "{std}: stdout {} stderr {}", stdout(&o), stderr(&o));
    }
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
    let o = cplusp(&["gate", "-p", root().to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("Use -p or --, not both."), "{}", stderr(&o));
}

/// Without the plugin most rows have no check behind them. An "ok" from such a run would mean nothing,
/// so the gate refuses the run. Decision 0025.
#[test]
fn gate_refuses_a_run_that_cannot_enforce_every_row() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stdout(&o).trim(), "", "nothing on stdout for a refused run");
    let err = stderr(&o);
    let line = err.lines().find(|l| l.starts_with("not enforced: no such check ")).expect(&err);
    assert!(line.contains("cplusp-matcher"), "{line}");
    assert!(line.ends_with(". The gate refuses a run that cannot enforce every row. Build the plugin and pass --plugin PATH."), "{line}");
}

/// With the plugin every row has its check, so a clean run says nothing on stderr.
#[test]
fn gate_with_the_plugin_is_silent_on_stderr() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert_eq!(stderr(&o).trim(), "", "a complete run has nothing to warn about");
}

/// With `-p` the flags come from the database. The gate judges them the same way, and refuses a response file it cannot read.
#[test]
fn gate_reads_the_flags_of_the_compile_database() {
    if !clang_tidy_available() {
        return;
    }
    let file = root().join("rules/goto/allowed.cpp");
    let file = file.to_str().unwrap();
    let root = root();
    let dir = root.to_str().unwrap();
    let float = "not allowed with the gate. It changes floating-point results, and the proofs assume IEEE 754 round to nearest.";
    for (entry, code, expected) in [
        (format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off -ffast-math -c {file} -o /tmp/allowed.o", "file": "{file}"}}"#), 2, format!("-ffast-math: {float}")),
        (format!(r#"{{"directory": "{dir}", "arguments": ["clang++", "-std=c++20", "-ffp-contract=off", "-c", "{file}"], "file": "{file}"}}"#), 2, "-std=c++20: not allowed with the gate. The proofs assume C++23 or later.".to_string()),
        (format!(r#"{{"directory": "{dir}", "command": "clang++ @flags.rsp -c {file}", "file": "{file}"}}"#), 2, "@flags.rsp: not allowed with the gate. The gate cannot read a response file.".to_string()),
        (format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off -c {file} -o /tmp/allowed.o", "file": "{file}"}}"#), 0, String::new()),
    ] {
        let build = tempfile::tempdir().unwrap();
        std::fs::write(build.path().join("compile_commands.json"), format!("[{entry}]")).unwrap();
        let o = gated(&["-p", build.path().to_str().unwrap(), file]);
        assert_eq!(o.status.code(), Some(code), "{entry}: stdout {} stderr {}", stdout(&o), stderr(&o));
        if code == 2 {
            assert_eq!(stdout(&o).trim(), "", "{entry}: nothing on stdout for a refused build");
            assert!(stderr(&o).lines().any(|l| l == expected), "{entry}: stderr {}", stderr(&o));
        } else {
            assert_eq!(stdout(&o).trim(), "ok: no findings", "{entry}");
        }
    }
}

/// A diagnostic pragma silences a compiler warning the policy relies on. Like NOLINT, it is a finding.
#[test]
fn gate_treats_a_diagnostic_pragma_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("pragma.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    for line in [2, 3, 4] {
        let expected = format!("pragma.cpp:{line}: pragma diagnostic: not allowed in verified code. It silences the gate.");
        assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(&expected)), "{out}");
    }
}

/// The preprocessor accepts spellings a text scan misses: a line splice, a comment between tokens, a digraph,
/// a macro from the command line, and the Microsoft form. The gate reads the preprocessor's view, so each is a finding.
#[test]
fn gate_sees_every_spelling_of_a_diagnostic_pragma() {
    if !clang_tidy_available() {
        return;
    }
    let pragma = "pragma diagnostic: not allowed in verified code. It silences the gate.";
    let f = fixture("pragma-spellings.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    for line in [3, 4, 5] {
        let expected = format!("pragma-spellings.cpp:{line}: {pragma}");
        assert!(stdout(&o).lines().any(|l| l.ends_with(&expected)), "{}", stdout(&o));
    }
    let f = fixture("define-pragma.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", r#"-DSILENCE=_Pragma("clang diagnostic ignored \"-Wreturn-stack-address\"")"#]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.ends_with(&format!("define-pragma.cpp:2: {pragma}"))), "{}", stdout(&o));
    let f = fixture("ms-pragma.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-fms-extensions"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.ends_with(&format!("ms-pragma.cpp:2: {pragma}"))), "{}", stdout(&o));
    let f = fixture("includes-spliced.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.ends_with("spliced-system-header.h:2: pragma system_header: not allowed in verified code. It silences the gate.")), "{}", stdout(&o));
    // A comment is not a pragma.
    let f = fixture("comment-mentions-pragma.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
}

/// A `#line` directive moves the gate's view of file and line, and can name a pseudo-file to hide behind.
/// It is a finding, and what follows it is still judged under the name it gave.
#[test]
fn gate_treats_a_line_directive_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("line-directive.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    assert!(out.lines().any(|l| l.ends_with("line-directive.cpp:2: line directive: not allowed in verified code. It moves the gate's view.")), "{out}");
    assert!(out.lines().any(|l| l.ends_with("<x>:1: pragma diagnostic: not allowed in verified code. It silences the gate.")), "{out}");
    let f = fixture("line-system.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.ends_with("line-system.cpp:2: line directive: not allowed in verified code. It moves the gate's view.")), "{}", stdout(&o));
}

/// A line marker written in the source, `# 1 "x" 1 3`, looks like the preprocessor's own. It declares the rest of the file
/// a system header, which clang-tidy does not judge, and the output alone cannot tell it from a real include. The source text can.
#[test]
fn gate_treats_a_forged_line_marker_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    // The plain spelling, one in a header, and the spellings a text scan forgets: a block comment before the `#`, a digraph,
    // a line splice after the `#`, and a comment between the `#` and the number. Each is a directive to the preprocessor.
    for (file, at) in [
        ("forged-marker.cpp", "forged-marker.cpp:2"),
        ("includes-forged.cpp", "forged-marker.h:2"),
        ("forged-comment.cpp", "forged-comment.cpp:2"),
        ("forged-digraph.cpp", "forged-digraph.cpp:2"),
        ("forged-splice.cpp", "forged-splice.cpp:2"),
        ("forged-inner-comment.cpp", "forged-inner-comment.cpp:2"),
        // A raw string holds a `/*` that is no comment. Only the compiler's own lexer reads it right, decision 0036.
        ("forged-raw-string.cpp", "forged-raw-string.cpp:5"),
        // Lines that end in a bare carriage return, and a comment whose text looks like a lexer's own record. The plugin reads the
        // directives from the preprocessor itself, decision 0037, so no reader of its output sits between.
        ("forged-cr.cpp", "forged-cr.cpp:2"),
        ("forged-loc-comment.cpp", "forged-loc-comment.cpp:2"),
    ] {
        let f = fixture(file);
        let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
        assert_eq!(o.status.code(), Some(1), "{file}: stdout: {} stderr: {}", stdout(&o), stderr(&o));
        let out = stdout(&o);
        let expected = format!("{at}: line directive: not allowed in verified code. It moves the gate's view.");
        assert!(out.lines().any(|l| l.ends_with(&expected)), "{file}: {out}");
    }
}

/// A line marker that names the file by its own path and flags it a system header, `# 3 "this file" 3`, is a line directive like
/// any other. It is the one spelling that looks like the note `#pragma GCC system_header` leaves behind, so the plugin must tell them
/// apart. The file is written at test time, because the marker must hold the file's own path.
#[test]
fn gate_treats_a_marker_that_names_the_file_itself_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-own-name-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("forged-own-name.cpp");
    std::fs::write(&f, format!("#include <cstdint>\n# 3 \"{}\" 3\nstruct S {{ uint32_t x : 3; }};\n", f.display())).unwrap();
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    assert!(out.lines().any(|l| l.ends_with("forged-own-name.cpp:2: line directive: not allowed in verified code. It moves the gate's view.")), "{out}");
    // The marker is a line directive and nothing else. No pragma wrote it.
    assert!(!out.contains("pragma system_header"), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The sequencing check counts a callee that writes a global in its body as a change, with or without a `modifies` line, and whether
/// or not the row `global_state` is enforced. Decision 0036 says a callee that writes a global changes state, and a team that loosens
/// one row must not loosen another.
#[test]
fn the_sequencing_check_reads_a_callees_body_under_a_loosened_state_row() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("sequencing-through-bodies.cpp");
    let team = fixture("team-loosen-state.yaml");
    let plugin = plugin();
    for policy in [None, Some(team.to_str().unwrap())] {
        let mut args = vec!["gate", "--plugin", plugin.to_str().unwrap()];
        if let Some(p) = policy {
            args.extend(["--policy", p]);
        }
        args.extend([f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
        let o = cplusp(&args);
        let out = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{policy:?}: stdout: {out} stderr: {}", stderr(&o));
        assert!(out.lines().any(|l| l.contains("sequencing-through-bodies.cpp:21: Two changes of state in one expression")), "{policy:?}: {out}");
        // The function the source names changes nothing. An override of it writes a global, and a call through the base may run it.
        assert!(out.lines().any(|l| l.contains("sequencing-through-bodies.cpp:40: Two changes of state in one expression")), "{policy:?}: {out}");
        // The writer sits behind code the compiler wrote, a lambda inside a std call and a copy of a container.
        assert!(out.lines().any(|l| l.contains("sequencing-through-bodies.cpp:52: Two changes of state in one expression")), "{policy:?}: {out}");
        assert!(out.lines().any(|l| l.contains("sequencing-through-bodies.cpp:69: Two changes of state in one expression")), "{policy:?}: {out}");
    }
}

/// A header included twice holds the same lines twice. A virtual call in the second inclusion is a call the tree wrote, and the gate
/// reads it there, decision 0037. Its finding names the header's line.
#[test]
fn gate_reads_a_virtual_call_in_the_second_inclusion_of_a_header() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("includes-twice.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    assert!(out.lines().any(|l| l.contains("twice-step.h:6: ") && l.ends_with("total changes, and the modifies line does not list it.")), "{out}");
}

/// The directives are read under the build's own flags, decision 0037. With `-trigraphs`, `??=` is `#`, and the marker it starts
/// is the forged one. A reader with flags of its own would not see it.
#[test]
fn gate_reads_directives_under_the_builds_flags() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("forged-trigraph.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-trigraphs"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    assert!(out.lines().any(|l| l.ends_with("forged-trigraph.cpp:2: line directive: not allowed in verified code. It moves the gate's view.")), "{out}");
}

/// `__pragma` expands macros before the pragma runs, so its words are the ones the preprocessor hands on, not the ones in the source.
/// A macro or a flag that turns `once` into a diagnostic pragma silences a row, and the gate must name what runs, decision 0038.
#[test]
fn gate_reads_the_words_a_pragma_runs_with() {
    if !clang_tidy_available() {
        return;
    }
    for (file, extra) in [("pragma-once-macro.cpp", None), ("pragma-once-flag.cpp", Some("-Donce=clang diagnostic ignored \"-Wreturn-stack-address\""))] {
        let f = fixture(file);
        let mut args = vec![f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-fms-extensions"];
        args.extend(extra);
        let o = gated(&args);
        let out = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{file}: stdout: {out} stderr: {}", stderr(&o));
        let line = if extra.is_some() { 2 } else { 3 };
        let expected = format!("{file}:{line}: pragma diagnostic: not allowed in verified code. It silences the gate.");
        assert!(out.lines().any(|l| l.ends_with(&expected)), "{file}: {out}");
    }
}

/// A `#line` directive may give a file name with a tab in it. The findings after it still print under that name.
#[test]
fn gate_prints_findings_under_a_file_name_with_a_tab() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("line-tab.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    assert!(out.lines().any(|l| l.ends_with("line-tab.cpp:2: line directive: not allowed in verified code. It moves the gate's view.")), "{out}");
    assert!(out.lines().any(|l| l.ends_with("a\tb:7: pragma clang fp: not allowed in verified code. It changes the build the proofs assume.")), "{out}");
}

/// A backslash in a header name is read by the compiler in a way of its own, and the dependency list prints it as a slash. A header
/// could hide from the NOLINT scan behind its twin. The include is refused, decision 0038. The files are written at test time.
#[test]
fn gate_refuses_a_header_name_with_a_backslash() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-backslash-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("back")).unwrap();
    std::fs::write(dir.join("back\\slash.h"), "#include <cstdint>\nint plain();  // NOLINT\n").unwrap();
    std::fs::write(dir.join("back").join("slash.h"), "#include <cstdint>\n").unwrap();
    let main = dir.join("includes-backslash.cpp");
    std::fs::write(&main, "#include <cstdint>\n#include \"back\\slash.h\"\nint32_t f() { return 0; }\n").unwrap();
    let o = gated(&[main.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let expected = "includes-backslash.cpp:2: include: a header name with a backslash is not allowed in verified code. The compiler may read it as another file.";
    assert!(out.lines().any(|l| l.ends_with(expected)), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The flags that write a dependency file are the build's business, also in their joined spelling. The gate's own dependency run
/// drops them, so they neither write a file nor hide the list.
#[test]
fn gate_drops_the_flags_that_write_a_file() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-mf-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mf = format!("-MF{}", dir.join("deps.d").display());
    let o = gated(&["rules/goto/allowed.cpp", "--", "-std=c++23", "-ffp-contract=off", "-MMD", &mf]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let _ = std::fs::remove_dir_all(&dir);
}

/// The dependency list escapes a space, `#` and `$`, and not a tab. A tab in a header path would split the name, and files named after
/// the pieces would stand in for the header in the NOLINT scan. A list with any white space but a space and a line break is refused.
/// The files are written at test time.
#[test]
fn gate_refuses_a_dependency_list_it_cannot_read() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-tab-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("di\tr")).unwrap();
    std::fs::create_dir_all(dir.join("r")).unwrap();
    std::fs::write(dir.join("di\tr").join("x.h"), "#include <cstdint>\nint dr();  // NOLINT\n").unwrap();
    std::fs::write(dir.join("di"), "").unwrap();
    std::fs::write(dir.join("r").join("x.h"), "").unwrap();
    let main = dir.join("tab-dir.cpp");
    std::fs::write(&main, "#include <cstdint>\n#include \"di\tr/x.h\"\nint32_t f() { return 0; }\n").unwrap();
    let plugin = plugin();
    let o = Command::new(env!("CARGO_BIN_EXE_cplusp"))
        .args(["gate", "--plugin", plugin.to_str().unwrap(), "tab-dir.cpp", "--", "-std=c++23", "-ffp-contract=off"])
        .current_dir(&dir)
        .output()
        .expect("cplusp runs");
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).lines().any(|l| l == "cannot preprocess tab-dir.cpp: the dependency list holds a name the gate cannot read."), "{}", stderr(&o));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A system header may change the warnings of the code that includes it: a diagnostic pragma that no push and pop of its own encloses
/// stays in force after the header ends. It silences a row in user code, so it is refused at the include that brings it in. The files
/// are written at test time.
#[test]
fn gate_refuses_a_system_header_that_changes_the_warnings_of_its_includer() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-leak-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("sys")).unwrap();
    std::fs::write(dir.join("sys").join("leak.h"), "#pragma clang diagnostic ignored \"-Wreturn-stack-address\"\n").unwrap();
    std::fs::write(dir.join("sys").join("tidy.h"), "#pragma clang diagnostic push\n#pragma clang diagnostic ignored \"-Wreturn-stack-address\"\n#pragma clang diagnostic pop\n").unwrap();
    let main = dir.join("includes-leak.cpp");
    std::fs::write(&main, "#include <cstdint>\n#include <leak.h>\n#include <tidy.h>\nconst int32_t& f() {\n  int32_t x = 1;\n  return x;\n}\n").unwrap();
    let sys = dir.join("sys");
    let o = gated(&[main.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-isystem", sys.to_str().unwrap()]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let expected = "includes-leak.cpp:2: pragma diagnostic: a system header changes the warnings of the code that includes it. It silences the gate.";
    assert!(out.lines().any(|l| l.ends_with(expected)), "{out}");
    // A header that restores what it changed leaves the includer alone.
    assert!(!out.lines().any(|l| l.contains("includes-leak.cpp:3:")), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The gate asks the compiler what the warnings are when user code resumes after a system header, decision 0038. A pair of headers
/// may pop the includer's push and change a warning, and a pair may change a warning inside a push and pop of the outer one. Only the
/// first changes what user code sees. A header that `-include` brings in is refused at the top of the file. The files are written at
/// test time.
#[test]
fn gate_asks_the_compiler_whether_a_system_header_changed_the_warnings() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-leak2-{}", std::process::id()));
    let sys = dir.join("sys");
    std::fs::create_dir_all(&sys).unwrap();
    let ignore = "#pragma clang diagnostic ignored \"-Wreturn-stack-address\"\n";
    std::fs::write(sys.join("pusher.h"), "#pragma clang diagnostic push\n#include <evil.h>\n").unwrap();
    std::fs::write(sys.join("evil.h"), format!("#pragma clang diagnostic pop\n{ignore}#pragma clang diagnostic push\n")).unwrap();
    std::fs::write(sys.join("outer.h"), "#pragma clang diagnostic push\n#include <inner.h>\n#pragma clang diagnostic pop\n").unwrap();
    std::fs::write(sys.join("inner.h"), ignore).unwrap();
    std::fs::write(sys.join("leak.h"), ignore).unwrap();
    let body = "const int32_t& f() {\n  int32_t x = 1;\n  return x;\n}\n";
    let leaks = dir.join("pair-leaks.cpp");
    std::fs::write(&leaks, format!("#include <cstdint>\n#include <pusher.h>\n{body}")).unwrap();
    let encloses = dir.join("pair-encloses.cpp");
    std::fs::write(&encloses, format!("#include <cstdint>\n#include <outer.h>\n{body}")).unwrap();
    let flagged = dir.join("flag-includes.cpp");
    std::fs::write(&flagged, format!("#include <cstdint>\n{body}")).unwrap();
    let message = "pragma diagnostic: a system header changes the warnings of the code that includes it. It silences the gate.";
    let run = |file: &Path, extra: &[&str]| {
        let mut args = vec![file.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-isystem", sys.to_str().unwrap()];
        args.extend_from_slice(extra);
        gated(&args)
    };
    let o = run(&leaks, &[]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "pair-leaks: stdout: {out} stderr: {}", stderr(&o));
    assert!(out.lines().any(|l| l.ends_with(&format!("pair-leaks.cpp:2: {message}"))), "pair-leaks: {out}");
    // The outer header pops what the inner one changed. The row still sees the return, and nothing leaked.
    let o = run(&encloses, &[]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "pair-encloses: stdout: {out} stderr: {}", stderr(&o));
    assert!(!out.contains("a system header changes the warnings"), "pair-encloses: {out}");
    assert!(out.lines().any(|l| l.contains("pair-encloses.cpp:5: ")), "pair-encloses: the row must still see the return: {out}");
    let o = run(&flagged, &["-include", "leak.h"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "flag-includes: stdout: {out} stderr: {}", stderr(&o));
    assert!(out.lines().any(|l| l.ends_with(&format!("flag-includes.cpp:1: {message}"))), "flag-includes: {out}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// clang's driver loads `h.h.pch` in place of `h.h` when it sits beside it, and a diagnostic pragma in the header then never reaches a
/// callback. The plugin asks the compiler whether it loaded a precompiled header, decision 0038, and refuses the run if it did. The files
/// are written at test time.
#[test]
fn gate_refuses_a_precompiled_header_that_the_compiler_loads_on_its_own() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-pch-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let header = dir.join("h.h");
    std::fs::write(&header, "#pragma clang diagnostic ignored \"-Wreturn-stack-address\"\n").unwrap();
    let built = Command::new("clang++-18")
        .args(["-x", "c++-header", "-std=c++23", "-ffp-contract=off"])
        .arg(&header)
        .arg("-o")
        .arg(dir.join("h.h.pch"))
        .output()
        .expect("clang++-18 runs");
    assert!(built.status.success(), "the precompiled header must build: {}", String::from_utf8_lossy(&built.stderr));
    let main = dir.join("uses-pch.cpp");
    std::fs::write(&main, "#include <cstdint>\nconst int32_t& f() {\n  int32_t x = 1;\n  return x;\n}\n").unwrap();
    let o = gated(&[main.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-include", header.to_str().unwrap()]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    let expected = "uses-pch.cpp:1: include: a precompiled header is loaded. It carries state from an earlier run of the compiler.";
    assert!(out.lines().any(|l| l.ends_with(expected)), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A range-for over a range through a const handle calls the range's `begin` and `end`. A non-const one outside std is a non-const
/// call on what the handle owns, decision 0040, and the finding sits at the `for`.
#[test]
fn a_range_for_over_a_const_handle_calls_only_const_begin_and_end() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("range-begin-writes.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    assert!(out.lines().any(|l| field(l, "rule") == "unique_ptr" && field(l, "line") == "19"), "{out}");
}

/// A value that carries a way to write is no read, decision 0041: a const method's result that hands out a pointer, a reference or a
/// span, a copy of a type with a pointer member, a const reference to one. The types come from a library header, which no row judges,
/// so the const-handle check is the only guard. A read that hands out nothing stays clean.
#[test]
fn what_carries_a_way_to_write_is_no_read() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("const-carriers.cpp");
    let sys = fixture("carriers");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-isystem", sys.to_str().unwrap()]);
    let out = stdout(&o);
    let found: BTreeSet<usize> = out.lines().filter(|l| field(l, "rule") == "unique_ptr").map(|l| field(l, "line").parse::<usize>().unwrap()).collect();
    assert_eq!(found, BTreeSet::from([7, 8, 9, 13, 18]), "{out}");
}

/// A `begin` declared in a `namespace std` that the file opens itself is the file's own, and it may write. The location decides, not
/// the namespace, as for every other test of std.
#[test]
fn a_range_for_trusts_only_a_begin_of_the_library() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("std-begin.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert!(out.lines().any(|l| field(l, "rule") == "unique_ptr" && field(l, "line") == "21"), "{out}");
}

/// A library type counts by what it holds, decision 0043. A view, a proxy reference and a type-erased box each hold a pointer to
/// non-const whatever their arguments say, so a copy of one out of a const handle is no read. A copy of a container that owns its
/// elements stays clean.
#[test]
fn a_library_type_counts_by_what_it_holds() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("const-library-carriers.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let found: BTreeSet<usize> = out.lines().filter(|l| field(l, "rule") == "unique_ptr").map(|l| field(l, "line").parse::<usize>().unwrap()).collect();
    assert_eq!(found, BTreeSet::from([10, 15, 20, 25]), "{out}");
}

/// The library is a place, and an analysis that cannot finish refuses, decisions 0036 and 0043. A `deque` that the file declares in
/// `namespace std` is the file's own, so its writing `at` is no element access. A type the check cannot see whole carries a way to write.
/// A mutable field stays writable through a const reference. A constructor of the library may call a method of the file on its
/// argument, as an engine calls `generate`, so it reads only a value of its own type or of its type arguments. A cast to an integer is
/// no read. A type of the file copies through its own constructor, which may write, so a library constructor reads only a number or
/// a value of the library, decision 0045. A library type that holds a type of the file is no value of the library, decision 0046,
/// and a member class of a library type, a template or not, holds what the type around it holds.
#[test]
fn the_const_handle_check_trusts_the_library_by_place_and_refuses_what_it_cannot_see() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("const-edges.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let found: BTreeSet<usize> = out.lines().filter(|l| field(l, "rule") == "unique_ptr").map(|l| field(l, "line").parse::<usize>().unwrap()).collect();
    assert_eq!(found, BTreeSet::from([21, 30, 43, 60, 65, 80, 86, 91, 108, 153]), "{out}");
}

/// Any pragma but `once` changes the build the proofs assume, or silences the gate. Two that turn contraction back on
/// behind the flags: clang's own and the standard's. The message names the pragma by its first two words.
#[test]
fn gate_treats_any_other_pragma_as_a_finding() {
    if !clang_tidy_available() {
        return;
    }
    for (file, name) in [("pragma-fp.cpp", "pragma clang fp"), ("pragma-stdc.cpp", "pragma STDC FP_CONTRACT"), ("pragma-pack.cpp", "pragma pack")] {
        let f = fixture(file);
        let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
        assert_eq!(o.status.code(), Some(1), "{file}: stdout: {} stderr: {}", stdout(&o), stderr(&o));
        let out = stdout(&o);
        let expected = format!("{file}:2: {name}: not allowed in verified code. It changes the build the proofs assume.");
        assert!(out.lines().any(|l| l.ends_with(&expected)), "{file}: {out}");
    }
}

/// A team may loosen a row to allow. When the row claims node kinds, those kinds are allowed too, or the loosening
/// would refuse the same lines under `unlisted` and the documented feature would be a lie.
#[test]
fn a_loosened_row_that_claims_kinds_allows_them() {
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-loosen.yaml");
    let banned = root().join("rules/goto/banned.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--policy", team.to_str().unwrap(), "--plugin", plugin.to_str().unwrap(), banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {out} stderr: {}", stderr(&o));
    assert!(!out.contains("GotoStmt") && !out.contains("LabelStmt"), "a loosened goto is no unlisted construct: {out}");
}

/// A team that loosens the allowlist itself keeps every ban. The kinds a row claims stay with the row, decision 0036.
#[test]
fn a_loosened_allowlist_keeps_every_ban() {
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-loosen-unlisted.yaml");
    let banned = root().join("rules/goto/banned.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--policy", team.to_str().unwrap(), "--plugin", plugin.to_str().unwrap(), banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    assert!(out.lines().any(|l| l.ends_with("banned.cpp:4: `goto`: not allowed in verified code. No benefit. Use a loop. The construct is GotoStmt.")), "{out}");
}

/// The gate runs the compiler itself and reads what it reports, decision 0038. A flag that changes what the compiler reads or reports
/// would leave the gate blind or make it judge something else. The run is refused.
#[test]
fn gate_refuses_flags_that_change_what_the_compiler_reports() {
    if !clang_tidy_available() {
        return;
    }
    for flag in ["-E", "-P", "-Wp,-P", "-dM", "-M", "-MM", "-MV", "-Xpreprocessor", "-Xclang", "-include-pch", "-fmodules", "-fmodule-file=m.pcm", "-###", "-fdriver-only"] {
        let o = gated(&["rules/goto/allowed.cpp", "--", "-std=c++23", "-ffp-contract=off", flag]);
        assert_eq!(o.status.code(), Some(2), "{flag}: stdout {} stderr {}", stdout(&o), stderr(&o));
        assert_eq!(stdout(&o).trim(), "", "{flag}: nothing on stdout for a refused run");
        let expected = format!("{flag}: not allowed with the gate. It changes what the compiler reads or reports, and the gate runs the compiler itself.");
        assert!(stderr(&o).lines().any(|l| l == expected), "{flag}: stderr {}", stderr(&o));
    }
}

/// A raw string can hold text that looks like a line marker of the preprocessor. It is no marker, and it must not make a header look
/// like a system header to the gate. The plugin reads the pragma from the preprocessor itself, and the NOLINT scan reads the files the
/// compiler's include graph names, decision 0038. The files are written at test time, because the fake marker holds the header's path.
#[test]
fn gate_finds_a_system_header_pragma_behind_a_marker_in_a_raw_string() {
    if !clang_tidy_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("cplusp-raw-marker-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let header = dir.join("hidden.hpp");
    std::fs::write(&header, "#pragma GCC system_header\n#include <cstdint>\nstruct Hidden { uint32_t value : 3; };  // NOLINT\n").unwrap();
    let main = dir.join("raw-marker.cpp");
    let text = format!(
        "#include <cstdint>\nstatic_assert(sizeof(R\"(\n# 1 \"{}\" 1 3\n)\") > 0);\n#include \"hidden.hpp\"\nuint32_t low(Hidden h) {{ return h.value; }}\n",
        header.display()
    );
    std::fs::write(&main, text).unwrap();
    let o = gated(&[main.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {out} stderr: {}", stderr(&o));
    for expected in [
        "hidden.hpp:1: pragma system_header: not allowed in verified code. It silences the gate.",
        "hidden.hpp:3: NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.",
    ] {
        assert!(out.lines().any(|l| l.ends_with(expected)), "{expected}: {out}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A file the preprocessor cannot read cannot be judged. The message has the shape of the other refusals.
#[test]
fn gate_names_a_missing_include() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("missing-include.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    let line = err.lines().find(|l| l.starts_with("cannot preprocess crates/cplusp/tests/fixtures/missing-include.cpp: ")).expect(&err);
    assert!(line.contains("nope.h"), "{line}");
}

/// clang-tidy runs every database entry of a file, so the gate judges every one. A command with shell quoting
/// is refused, because the gate cannot read it the way the shell would. A `--config` file is a response file by another name.
#[test]
fn gate_judges_every_database_entry_and_refuses_what_it_cannot_read() {
    if !clang_tidy_available() {
        return;
    }
    let root = root();
    let file = root.join("rules/goto/allowed.cpp");
    let file = file.to_str().unwrap();
    let dir = root.to_str().unwrap();
    let float = "not allowed with the gate. It changes floating-point results, and the proofs assume IEEE 754 round to nearest.";
    let clean = format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off -c {file}", "file": "{file}"}}"#);
    for (entries, code, expected) in [
        // The second entry carries the bad flag.
        (format!(r#"{clean}, {{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off -ffast-math -c {file}", "file": "{file}"}}"#), 2, format!("-ffast-math: {float}")),
        (format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off '-DFOO' '-ffast-math' -c {file}", "file": "{file}"}}"#), 2, format!("{file}: the command in compile_commands.json has shell quoting, which the gate cannot read. Use arguments.")),
        (format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off --config fast.cfg -c {file}", "file": "{file}"}}"#), 2, "--config: not allowed with the gate. The gate cannot read a config file.".to_string()),
        // Dependency flags are the build's business, and a phony target is not a header.
        (format!(r#"{{"directory": "{dir}", "command": "clang++ -std=c++23 -ffp-contract=off -MD -MP -MT allowed.o -MF /dev/null -c {file}", "file": "{file}"}}"#), 0, String::new()),
    ] {
        let build = tempfile::tempdir().unwrap();
        std::fs::write(build.path().join("compile_commands.json"), format!("[{entries}]")).unwrap();
        let o = gated(&["-p", build.path().to_str().unwrap(), file]);
        assert_eq!(o.status.code(), Some(code), "{entries}: stdout {} stderr {}", stdout(&o), stderr(&o));
        if code == 2 {
            assert!(stderr(&o).lines().any(|l| l == expected), "{entries}: stderr {}", stderr(&o));
        } else {
            assert_eq!(stdout(&o).trim(), "ok: no findings", "{entries}");
        }
    }
    // The same config file refusal after `--`, in both spellings.
    for (flag, shown) in [("--config", "--config"), ("--config=fast.cfg", "--config=fast.cfg")] {
        let o = gated(&["rules/goto/allowed.cpp", "--", "-std=c++23", "-ffp-contract=off", flag, "fast.cfg"]);
        assert_eq!(o.status.code(), Some(2), "{flag}: stdout {} stderr {}", stdout(&o), stderr(&o));
        let expected = format!("{shown}: not allowed with the gate. The gate cannot read a config file.");
        assert!(stderr(&o).lines().any(|l| l == expected), "{flag}: stderr {}", stderr(&o));
    }
    // The given path may spell the file with `..`. The entry still matches.
    let build = tempfile::tempdir().unwrap();
    std::fs::write(build.path().join("compile_commands.json"), format!("[{clean}]")).unwrap();
    let o = gated(&["-p", build.path().to_str().unwrap(), "rules/goto/../goto/allowed.cpp"]);
    assert_eq!(o.status.code(), Some(0), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
}

/// The gate judges the headers a file includes, outside the system paths, and scans them for suppressions too.
#[test]
fn gate_judges_and_scans_the_headers_a_file_includes() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("includes-banned.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.contains("banned-header.h:2: Unscoped `enum`: ")), "{}", stdout(&o));

    let f = fixture("includes-silenced.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let out = stdout(&o);
    for expected in [
        "silenced-header.h:1: pragma system_header: not allowed in verified code. It silences the gate.",
        "silenced-header.h:3: NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.",
    ] {
        assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{out}");
    }
}

#[test]
fn gate_refuses_a_plugin_that_does_not_load() {
    if !clang_tidy_available() {
        return;
    }
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "--plugin", "/nonexistent/libcplusp.so", f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stderr(&o).contains("plugin"), "{}", stderr(&o));
    assert_eq!(stdout(&o).trim(), "");
}

#[test]
fn policy_emit_turns_matcher_patterns_into_options_of_the_generic_check() {
    let o = cplusp(&["policy", "emit"]);
    assert!(o.status.success(), "stderr: {}", stderr(&o));
    let out = stdout(&o);
    let checks = out.lines().find(|l| l.starts_with("Checks:")).expect("Checks line");
    assert_eq!(checks.matches("cplusp-matcher").count(), 1, "{checks}");
    assert!(out.contains("  cplusp-matcher.unscoped_enum/1: 'enumDecl(unless(isScoped()), unless(isImplicit()))'"), "{out}");
    assert!(out.contains("  cplusp-matcher.lvalue_references/1: 'fieldDecl(hasType(referenceType()))'"), "{out}");
    // A row that claims node kinds names them as an option of the allowlist check, keyed by the row.
    assert!(out.contains("  cplusp-allowlist.exceptions: 'CXXThrowExpr,CXXTryStmt,CXXCatchStmt'"), "{out}");
}

#[test]
fn gate_refuses_a_policy_whose_matcher_does_not_parse() {
    if !clang_tidy_available() {
        return;
    }
    let policy = fixture("bad-matcher.yaml");
    let f = root().join("rules/goto/allowed.cpp");
    let o = cplusp(&["gate", "--plugin", plugin().to_str().unwrap(), "--policy", policy.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
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
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
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
    let o = gated(&["rules/goto/banned.cpp", "--", "-std=c++23", "-ffp-contract=off"]);
    assert_eq!(o.status.code(), Some(1), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    assert!(stdout(&o).lines().any(|l| l.starts_with("Not provable: rules/goto/banned.cpp:4: ")), "{}", stdout(&o));
}

#[test]
fn gate_names_a_missing_input_file() {
    if !clang_tidy_available() {
        return;
    }
    let o = gated(&["nope.cpp", "--", "-std=c++23", "-ffp-contract=off"]);
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
/// is reported on exactly the lines marked `// BANNED`, each by its own rule. A line that
/// a second row also refuses says so: `// BANNED also: other_rule`.
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
        let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), allowed.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
        assert_eq!(o.status.code(), Some(0), "{id}/allowed.cpp: stdout {} stderr {}", stdout(&o), stderr(&o));
        assert_eq!(stdout(&o).trim(), "", "{id}/allowed.cpp must produce no findings");

        let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
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
            .filter_map(|(i, l)| l.split_once("// BANNED").map(|(_, mark)| (i + 1, mark)))
            .flat_map(|(line, mark)| {
                let also = mark.split_once("also:").map(|(_, r)| r).unwrap_or("");
                std::iter::once(id.clone()).chain(also.split(',').map(str::trim).filter(|r| !r.is_empty()).map(String::from)).map(move |r| (r, line))
            })
            .collect();
        assert_eq!(reported, expected, "{id}/banned.cpp");
        checked += 1;
    }
    // Every rule the gate can enforce today has a pair: the upstream checks and the matcher patterns.
    for id in [
        "c_style_casts", "goto", "pointer_arithmetic", "reinterpret_const_cast", "varargs_coroutines", "uninitialised_variables",
        "missing_override", "function_like_macros", "downcasts", "raw_allocation", "return_ref_to_local", "rvalue_references",
        "unscoped_enum", "unions", "bitfields", "virtual_inheritance", "exceptions", "shared_ptr", "implicit_conversions",
        "function_pointers", "concurrency", "volatile", "inline_asm_intrinsics", "unreachable_assume", "longjmp",
        "raw_memory_ops", "launder_placement_new", "templates", "metaprogramming",
        "mutable_members", "multiple_inheritance", "operator_overloading", "iterators", "lambdas",
        "plain_int", "sign_compare", "evaluation_order",
        "implicit_narrowing", "sign_conversion", "widening_multiplication", "literal_shift",
        "member_init_order", "slicing", "virtual_call_in_constructor", "virtual_destructor", "raw_pointer", "containers",
        "switch_fallthrough", "switch_missing_case", "accumulate_init", "array_span",
        "double_equality", "double_expression", "rounding_mode", "global_constructors", "double_only", "inexact_literal", "unique_ptr", "static_local", "strings",
        "aliasing", "unlisted", "global_state", "iostreams", "builtins",
    ] {
        assert!(rules_dir.join(id).is_dir(), "no sample pair for rule {id}");
    }
    assert!(checked >= 66, "expected at least 66 sample pairs, found {checked}");
}


// ------------------------------------------------------------------ markers, decision 0039

/// The plugin reads the markers of include/cplusp.h. A finding takes the kind of the function that holds it, and the core decides
/// what each kind keeps. Every finding stands in verified code. A finding of a Trusted only row goes in a trusted body, here `new`
/// and a stream, and a ban stands there, here `goto`. Nothing of a row stands in plain code. Verified code may not call plain code.
#[test]
fn a_finding_takes_the_kind_of_the_function_that_holds_it() {
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    ] {
        assert!(out.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(expected)), "{expected}: {out}");
    }
    assert_eq!(out.lines().filter(|l| l.starts_with("Not provable: ")).count(), 8, "{out}");
}

/// Each function has its own kind, decision 0047. A local class, a lambda and an explicit specialization carry no marker of their own,
/// so they are verified inside a trusted body. A marked function whose first or last token is in a macro or another file is refused,
/// and its body is then verified. A function whose ends are in two files is refused whatever its kind, and code in a plain body is
/// plain, decision 0048. An abbreviated function template begins at its return type, decision 0049.
#[test]
fn a_finding_takes_the_kind_of_the_innermost_function_the_file_wrote() {
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
/// pointer to non-const can write. A forwarding reference that becomes a const reference cannot. Only that row counts here.
#[test]
fn the_impure_operator_check_judges_each_instantiation() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("templates-impure.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let found: BTreeSet<usize> = out.lines().filter(|l| field(l, "rule") == "operator_overloading").map(|l| field(l, "line").parse::<usize>().unwrap()).collect();
    assert_eq!(found, BTreeSet::from([8]), "{out}");
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

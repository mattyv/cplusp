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
    assert!(out.contains("google-readability-casting"), "{out}");
    assert!(out.contains("cppcoreguidelines-avoid-goto"), "{out}");
    assert!(out.contains("WarningsAsErrors: '*'"), "{out}");
    // A dormant check on an allow row never reaches the config.
    assert!(!out.contains("cppcoreguidelines-pro-bounds-constant-array-index"), "{out}");
    // Every check once.
    assert_eq!(out.matches("google-readability-casting").count(), 1, "{out}");
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
    let o = gated(&[banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
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
    for (file, at) in [("forged-marker.cpp", "forged-marker.cpp:2"), ("includes-forged.cpp", "forged-marker.h:2")] {
        let f = fixture(file);
        let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
        assert_eq!(o.status.code(), Some(1), "{file}: stdout: {} stderr: {}", stdout(&o), stderr(&o));
        let out = stdout(&o);
        let expected = format!("{at}: line directive: not allowed in verified code. It moves the gate's view.");
        assert!(out.lines().any(|l| l.ends_with(&expected)), "{file}: {out}");
    }
}

/// A flag that strips the line markers from the preprocessor output leaves the gate blind. The run is refused.
#[test]
fn gate_refuses_a_preprocessor_run_without_line_markers() {
    if !clang_tidy_available() {
        return;
    }
    for flag in ["-P", "-Wp,-P", "-dM", "-M", "-MM", "-###", "-fdriver-only"] {
        let o = gated(&["rules/goto/allowed.cpp", "--", "-std=c++23", "-ffp-contract=off", flag]);
        assert_eq!(o.status.code(), Some(2), "{flag}: stdout {} stderr {}", stdout(&o), stderr(&o));
        assert_eq!(stdout(&o).trim(), "", "{flag}: nothing on stdout for a refused run");
        let expected = "cannot preprocess rules/goto/allowed.cpp: the preprocessor output has no line marker for it";
        assert!(stderr(&o).lines().any(|l| l == expected), "{flag}: stderr {}", stderr(&o));
    }
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
        "aliasing",
    ] {
        assert!(rules_dir.join(id).is_dir(), "no sample pair for rule {id}");
    }
    assert!(checked >= 62, "expected at least 62 sample pairs, found {checked}");
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

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
    assert!(out.contains("\nExtraArgs: ['-Wreturn-stack-address', '-Wreorder-ctor', '-Wimplicit-fallthrough', '-Wswitch', '-Wunsequenced', '-Wglobal-constructors', '-Wunknown-attributes', '-Wignored-attributes']\n"), "{out}");
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
        // A 32-bit x86 target computes a double with x87, decision 0151.
        (vec!["-std=c++23", "-ffp-contract=off", "--target=i686-linux-gnu"], format!("--target=i686-linux-gnu: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-target", "i686-linux-gnu"], format!("-target: {float}")),
        // More ways to an x87 double, decision 0152.
        (vec!["-std=c++23", "-ffp-contract=off", "--target=i786-linux-gnu"], format!("--target=i786-linux-gnu: {float}")),
        (vec!["-std=c++23", "-ffp-contract=off", "-mno-sse2"], format!("-mno-sse2: {float}")),
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
        (vec!["-std=c++23", "-ffp-contract=off", "--no-warnings"], "--no-warnings: not allowed with the gate. It hides the compiler warnings the policy names.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "--std", "c++20"], "--std: not allowed with the gate. The proofs assume C++23 or later.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-ansi"], "-ansi: not allowed with the gate. The proofs assume C++23 or later.".to_string()),
        (vec!["-I", "-std=c++23", "-ffp-contract=off"], "-I: not allowed with the gate. It takes the next flag as its value, and the gate reads the flags as written.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-I"], "-I: not allowed with the gate. It takes the next flag as its value, and the gate reads the flags as written.".to_string()),
        (vec!["-std=c++23", "-ffp-contract=off", "-MJ", "x.json"], "-MJ: not allowed with the gate. It changes what the compiler reads or reports, and the gate runs the compiler itself.".to_string()),
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

/// The compiler can print a warning before its error. The message names the error, from the review of 0130. A linker flag is
/// unused when the gate lists the headers, so the compiler warns about it before it reads the file.
#[test]
fn gate_names_the_error_of_the_preprocessor_and_not_a_warning() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("missing-include.cpp");
    let o = gated(&[f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off", "-Wl,--foo"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {} stderr: {}", stdout(&o), stderr(&o));
    let err = stderr(&o);
    let line = err.lines().find(|l| l.starts_with("cannot preprocess crates/cplusp/tests/fixtures/missing-include.cpp: ")).expect(&err);
    assert!(line.ends_with("missing-include.cpp:1:10: fatal error: 'nope.h' file not found"), "{line}");
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

/// A view in a local does not hide the local that it views. When a team loosens array_span and raw_pointer, a return through a span
/// local or a pointer local of a local is still refused, decision 0182.
#[test]
fn a_view_local_does_not_hide_a_local() {
    if !clang_tidy_available() {
        return;
    }
    let team = fixture("team-loosen-views.yaml");
    let f = fixture("return-local-view.cpp");
    let o = gated(&["--policy", team.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let lines: BTreeSet<&str> = text
        .lines()
        .filter(|l| l.contains("Returning a reference or pointer to a local"))
        .filter_map(|l| l.split("return-local-view.cpp:").nth(1))
        .filter_map(|r| r.split(':').next())
        .collect();
    assert_eq!(lines, BTreeSet::from(["8", "14"]), "{text}");
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
/// pointer to non-const can write. A forwarding reference that becomes a const reference cannot. An operator in a template that
/// nothing instantiates is judged by its spelling, as before. Only that row counts here.
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
    assert_eq!(found, BTreeSet::from([8, 35, 39]), "{out}");
}

// ------------------------------------------------------------------ the translator, decisions 0056 and 0057

/// Dafny, from `$DAFNY`, the battery's install, or the path. None skips the test.
fn dafny() -> Option<PathBuf> {
    if let Ok(d) = std::env::var("DAFNY") {
        return Some(PathBuf::from(d));
    }
    let installed = PathBuf::from("/opt/dafny/dafny/dafny");
    if installed.exists() {
        return Some(installed);
    }
    Command::new("dafny").arg("--version").output().ok().filter(|o| o.status.success()).map(|_| PathBuf::from("dafny"))
}

/// Translate one fixture into a Dafny file, and give the gate's output and the path of the model.
fn model(name: &str, dir: &Path) -> (Output, PathBuf) {
    model_of(&fixture(name), dir)
}

/// Translate one file into a Dafny file.
fn model_of(f: &Path, dir: &Path) -> (Output, PathBuf) {
    let out = dir.join("model.dfy");
    let plugin = plugin();
    let o = cplusp(&["model", "--plugin", plugin.to_str().unwrap(), "--out", out.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    (o, out)
}

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
    assert!(refusals.iter().any(|l| l.ends_with("model-refuse.cpp:9: BinaryOperator <<: the translator has no rule for it yet.")), "{text}");
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
        assert!(model.contains(&format!("method {name}(")) || model.lines().any(|l| l.starts_with("method ") && l.contains(name)), "{name}: {model}");
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

/// The lines of the method named `c_{name}` in a model: its header and what follows up to the next method.
fn method_lines<'a>(model: &'a str, name: &str) -> Option<Vec<&'a str>> {
    let header = format!("method c_{name}(");
    let mut lines = model.lines().skip_while(|l| !l.starts_with(&header));
    let first = lines.next()?;
    Some(std::iter::once(first).chain(lines.take_while(|l| !l.starts_with("method "))).collect())
}

/// A method with a body.
fn full(model: &str, name: &str) -> bool {
    method_lines(model, name).is_some_and(|ls| ls.contains(&"{"))
}

/// A method with no contract and no body: it assumes nothing, decision 0058.
fn bare(model: &str, name: &str) -> bool {
    method_lines(model, name).is_some_and(|ls| ls[1..].iter().all(|l| l.trim().is_empty()))
}

/// Dafny's verdict on a model: did it pass, and what it said.
fn verify(dafny: &Path, model: &Path) -> (bool, String) {
    let v = Command::new(dafny).args(["verify"]).arg(model).output().unwrap();
    (v.status.success(), format!("{}{}", String::from_utf8_lossy(&v.stdout), String::from_utf8_lossy(&v.stderr)))
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
    for name in ["to_declared", "to_member", "twice", "shadow", "from_bool", "no_start", "two_names", "bad_contract", "refused_body", "defaulted"] {
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
    assert!(text.lines().any(|l| l.ends_with("model-seq-global.cpp:8: BinaryOperator =: the translator has no rule for it yet.")), "{text}");
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

/// Run `cplusp prove` on one fixture, with Dafny from the test's search, decision 0068.
fn prove(name: &str, extra: &[&str], dafny: &Path) -> Output {
    let f = fixture(name);
    let plugin = plugin();
    let mut args = vec!["prove", "--plugin", plugin.to_str().unwrap()];
    args.extend(extra.iter().copied());
    args.extend([f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    Command::new(env!("CARGO_BIN_EXE_cplusp")).args(&args).env("DAFNY", dafny).current_dir(root()).output().unwrap()
}

/// The line that follows the `Not proved:` line which ends with `head`, and the lines under it up to the next `Not proved:`.
fn under<'a>(text: &'a str, head: &str) -> Vec<&'a str> {
    let mut lines = text.lines().skip_while(|l| !(l.starts_with("Not proved: ") && l.ends_with(head)));
    assert!(lines.next().is_some(), "no line ends with {head}: {text}");
    lines.take_while(|l| l.starts_with("  ")).collect()
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
    assert!(lines.iter().any(|l| l.starts_with("  The contract line: ") && l.ends_with("model-clamp-wrong.cpp:5: ensures x < lo ==> result == hi")), "{text}");
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
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with("model-seq-wrong.cpp:6: the index may be out of range.")), "{text}");
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
    assert!(lines.iter().any(|l| l.starts_with("  The contract line: ") && l.ends_with("model-prove-loops.cpp:26: requires x > 0")), "{text}");
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
    for want in ["model-prove-places.cpp:8: the value may not fit uint32_t.", "model-prove-places.cpp:10: the value may not fit uint32_t."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
    let lines = under(&text, "model-prove-places.cpp:18: the index may be out of range.");
    assert!(lines.iter().any(|l| l.starts_with("  It assumes: ") && l.ends_with("model-prove-places.cpp:17: requires v[10] == 0")), "{text}");
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

/// A struct of scalars is a Dafny datatype, decision 0073. Field reads, braced values, nested structs and a copy to a parameter prove.
#[test]
fn structs_of_scalars_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-struct.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each struct with no rule is refused at its line, decision 0073.
#[test]
fn structs_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-struct-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, expected) in [
        (8, "Handle: the translator has no rule for it yet."),
        (18, "BinaryOperator =: the translator has no rule for it yet."),
        (22, "z in the contract is no field of the struct."),
        (28, "ImplicitValueInitExpr: the translator has no rule for it yet."),
        (33, "p is a reference parameter that the modifies line does not name."),
    ] {
        let want = format!("model-struct-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 5, "{text}");
}

/// A destructor and an operator() of a plain struct have models. Their names reach the Dafny text as words, never as the C++
/// spelling, decisions 0069 and 0178.
#[test]
fn a_member_function_reaches_the_dafny_text_as_a_word_whatever_its_name() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, out) = model("model-member-names.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Not provable: "), "{text}");
    let dafny = std::fs::read_to_string(out).unwrap();
    assert!(dafny.contains("method c_D'dtor(") && dafny.contains("method c_D'call("), "{dafny}");
    assert!(!dafny.contains('~'), "{dafny}");
}

/// An optional scalar is a Dafny Option, decision 0075. Its reads in code and contracts, `std::nullopt`, the construction from a
/// value, a field, a copy and a call prove.
#[test]
fn optional_scalars_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-optional.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each read of an optional that may be empty is named at its line, in code and in a contract, decision 0075.
#[test]
fn prove_names_each_read_of_an_optional_that_may_be_empty() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-optional-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for line in [6, 9, 18] {
        let want = format!("model-optional-wrong.cpp:{line}: the optional may be empty or the pointer may be null here.");
        assert!(failed.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    // The ensures line reads the value of the empty optional that line 12 gives, so it cannot hold on that return either.
    let want = "model-optional-wrong.cpp:12: the ensures line may not hold on this return.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    // A value that the compiler turns into an optional is checked like any other value.
    let want = "model-optional-wrong.cpp:22: the value may not fit int32_t.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(failed.len(), 5, "{text}");
}

/// Each use of an optional with no rule is refused at its line, decision 0075. A construction from an expression of type
/// `std::nullopt_t` that is not `std::nullopt` itself is refused, so its argument cannot vanish from the model. An optional of a plain
/// struct has a rule since decision 0137, so `of_struct` is no longer refused.
#[test]
fn optionals_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-optional-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, expected) in [
        (6, "ImplicitCastExpr UserDefinedConversion: the translator has no rule for it yet."),
        (14, "CXXOperatorCallExpr: the translator has no rule for it yet."),
        (19, "CXXOperatorCallExpr: the translator has no rule for it yet."),
        (35, "CXXConstructExpr: the translator has no rule for it yet."),
        (39, "CXXConstructExpr: the translator has no rule for it yet."),
        (43, "a sequence or an optional made from one of another type or length."),
    ] {
        let want = format!("model-optional-refuse.cpp:{line}: {expected}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
}

/// A struct that holds a sequence, a recursive struct and a sequence of structs prove, decision 0076. Reads on a field or an
/// element, contracts on a path, a loop over the children and a recursion into a child.
#[test]
fn structs_that_hold_sequences_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-nodes.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// Each index into a nested sequence and a recursion that does not go down are named at their lines, decision 0076.
#[test]
fn prove_names_each_failed_read_and_measure_on_a_recursive_struct() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-nodes-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let index = "model-nodes-wrong.cpp:11: the index may be out of range.";
    assert_eq!(failed.iter().filter(|l| l.ends_with(index)).count(), 2, "{text}");
    let measure = "model-nodes-wrong.cpp:16: the decreases line may not decrease at this call.";
    assert!(failed.iter().any(|l| l.ends_with(measure)), "{text}");
    assert_eq!(failed.len(), 3, "{text}");
}

/// A struct that holds a sequence, directly or through a field, is refused as a local or a result, decision 0076.
#[test]
fn a_struct_that_holds_a_sequence_is_a_parameter_only() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-nodes-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for line in [15, 19, 24] {
        let want = format!("model-nodes-refuse.cpp:{line}: a struct that holds a sequence is in the subset only as a parameter that the function does not write.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 3, "{text}");
}

/// A struct or a field whose name Dafny cannot read is refused at the struct's line, as a function is, decision 0069. Found by the
/// review of decision 0076.
#[test]
fn a_struct_or_field_name_dafny_cannot_read_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-struct-names.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (line, name) in [(5, "a$b"), (10, "N$")] {
        let want = format!("model-struct-names.cpp:{line}: {name}: a name with a character Dafny cannot read.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// `empty()` and `subspan(k)` prove, in code and in contracts, through a recursion over a span, decision 0078.
#[test]
fn subspan_and_empty_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-subspan.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An offset past the end of a span is named at its line, decision 0078.
#[test]
fn prove_names_an_offset_that_may_be_past_the_end() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-subspan-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let want = "model-subspan-wrong.cpp:17: the offset may be past the end.";
    assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(failed.len(), 1, "{text}");
}

/// The forms of a span with no rule yet are refused at their lines, decision 0078.
#[test]
fn spans_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-subspan-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for line in [11, 16] {
        let want = format!("model-subspan-refuse.cpp:{line}: CXXMemberCallExpr: the translator has no rule for it yet.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// A contract calls the functions and predicates of the companion file, decision 0079: an integer function, a predicate on a
/// recursive struct, and a predicate in a requires line.
#[test]
fn specification_functions_from_the_companion_file_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A function with no body and an ensures line in the companion file is an axiom. Dafny proves a wrong body from it, and the run
/// must not say proved, decision 0079.
#[test]
fn prove_refuses_an_axiom_in_the_companion_file() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-axiom.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-axiom.spec.dfy:3: a function with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A call to a name that the companion file does not declare is refused at the contract line, decision 0079.
#[test]
fn a_call_to_a_name_the_companion_file_does_not_declare_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-spec-name.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let want = "model-spec-name.cpp:4: Min is no function of the companion file.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 1, "{text}");
}

/// A companion file that holds an attribute, a method or an assume is refused at each word, and then it declares no function,
/// decisions 0079 and 0099.
#[test]
fn a_companion_file_with_other_words_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-spec-words.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for (file, line, word) in [("model-spec-words.spec.dfy", 1, "{:"), ("model-spec-words.spec.dfy", 3, "method"), ("model-spec-words.spec.dfy", 6, "assume")] {
        let want = format!("{file}:{line}: {word}: a companion file can hold only functions, predicates and lemmas.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    let want = "model-spec-words.cpp:4: Max is no function of the companion file.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 4, "{text}");
}

/// A struct refused for its name leaves no method that names it, so prove ends with the refusals and does not fail on the Dafny
/// text. Found after decision 0078.
#[test]
fn prove_stops_at_the_refusal_of_a_struct_name() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-struct-names.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
}

/// The thin slice, decision 0056: radix_find proves end to end. Gate, translator and Dafny, from C++ with a contract and a companion
/// file of specification functions. The height bound is the rule of the battery case stack_depth.
#[test]
fn radix_find_proves_end_to_end() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-radix.cpp", &["--time-limit", "60"], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// The four companion files from the review of decision 0079 each made a wrong body prove. Each is now refused at the word that
/// hides an axiom or the model, and no run says proved, decision 0080.
#[test]
fn prove_refuses_each_companion_file_that_hid_an_axiom_or_the_model() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let word = |w: &str| format!("{w}: a companion file can hold only functions, predicates and lemmas.");
    let cases: [(&str, Vec<(u32, String)>); 4] = [
        ("unclosed", vec![(2, "a comment that does not end.".to_string())]),
        ("string", vec![(1, word("\"")), (2, word("{:"))]),
        ("nested", vec![(2, word("type")), (2, word("witness"))]),
        ("newtype", vec![(1, word("newtype")), (1, word("witness"))]),
    ];
    for (name, wants) in cases {
        let o = prove(&format!("model-spec-{name}.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert!(!text.contains("ok: proved"), "{name}: {text}");
        for (line, sentence) in wants {
            let want = format!("model-spec-{name}.spec.dfy:{line}: {sentence}");
            assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(&want)), "{want}: {text}");
        }
    }
}

/// A contract call that Dafny cannot resolve is named at its C++ line in the words of Dafny, and the run is not proved, with
/// exit 1. It is no failure of the tool, decision 0080.
#[test]
fn prove_names_a_resolution_error_at_its_line() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-arity.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-arity.cpp:3: Dafny says: wrong number of arguments";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.contains(want)), "{want}: {text}");
}

/// Two companion files from the second review made a wrong body prove: a lone carriage return hid an axiom from the scan, and a
/// function named Some changed the model's Some. Both are refused, and neither proves, decision 0083.
#[test]
fn prove_refuses_a_lone_carriage_return_and_a_name_of_the_model() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    for (name, want) in [
        ("cr", "model-spec-cr.spec.dfy:1: a character that a companion file cannot hold."),
        ("some", "model-spec-some.spec.dfy:1: Some: a name that the model uses."),
    ] {
        let o = prove(&format!("model-spec-{name}.cpp"), &[], &dafny);
        let text = stdout(&o);
        assert_eq!(o.status.code(), Some(1), "{name}: stdout: {text} stderr: {}", stderr(&o));
        assert!(!text.contains("ok: proved"), "{name}: {text}");
        assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A parse error in the companion file is the author's, named in its file in the words of Dafny, with exit 1, decision 0083.
#[test]
fn prove_names_a_parse_error_in_the_companion_file() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-brace.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!stderr(&o).contains("dafny failed"), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-brace.spec.dfy:2: Dafny says: rbrace expected.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// When Dafny verifies fewer items than the model has methods, and nothing else is wrong, prove says so in one line, decision 0083.
#[test]
fn prove_names_a_run_that_verified_too_few_items() {
    if dafny().is_none() || !clang_tidy_available() {
        return;
    }
    let o = prove("model-clamp.cpp", &[], &fixture("fake-dafny-few-verified.sh"));
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-clamp.cpp: Dafny verified fewer items than the model has methods: 0 for 1.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// Hex literals, exists, forall with two bound names, and true and false prove, decisions 0082 and 0084.
#[test]
fn hex_literals_exists_and_several_bound_names_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-quant.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A hex literal too large for uint64_t is refused, and a shift in a contract has no rule, decisions 0082 and 0088.
#[test]
fn a_hex_literal_too_large_and_a_shift_in_a_contract_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-quant-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-quant-refuse.cpp:4: a number above 18446744073709551615: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:9: the contract line has a form the translator cannot read.",
        "model-quant-refuse.cpp:15: an octal number: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:20: a number with the suffix e3: the translator has no rule for it yet.",
        "model-quant-refuse.cpp:25: a number with no digits after 0x: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 5, "{text}");
}

/// An error inside a function of the companion file prints in the words of Dafny, not as a return of a method, decision 0084.
#[test]
fn an_error_in_the_companion_file_prints_in_the_words_of_dafny() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-wording.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-wording.spec.dfy:1: Dafny says: a postcondition could not be proved on this return path.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("may not hold on this return"), "{text}");
}

/// A literal that is too large is an unknown token, never a token the grammar knows. Read as `::`, it would turn
/// `forall j 99999999999999999999 j > j` into `forall j :: j > j`, a requires line that is false. From the review of decision 0082.
#[test]
fn a_literal_that_is_too_large_never_stands_for_another_token() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-quant-junk.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-quant-junk.cpp:4: a number above 18446744073709551615: the translator has no rule for it yet.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
}

/// Slices in a contract prove: examples/recursion with Count(v[i..], x), and the size, an element and empty of a part, decision 0085.
#[test]
fn slices_in_a_contract_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-slice.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A slice that may start past the end is named at its contract line, decision 0085.
#[test]
fn prove_names_a_slice_that_may_start_past_the_end() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-slice-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-slice-wrong.cpp:6: the offset may be past the end.", "model-slice-wrong.cpp:8: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// Division and remainder truncate as in C++, in code and in contracts, signed and unsigned, decision 0088.
#[test]
fn division_truncates_as_in_cpp() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-div.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A divisor that may be zero, a quotient that may not fit, also for %, and a contract that expects Dafny's own division, are
/// each named at their lines, decision 0088.
#[test]
fn prove_names_a_division_that_may_fail() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-div-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-div-wrong.cpp:5: the divisor may be zero.",
        "model-div-wrong.cpp:5: the value may not fit int32_t.",
        "model-div-wrong.cpp:10: the value may not fit int32_t.",
        "model-div-wrong.cpp:16: the ensures line may not hold on this return.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 4, "{text}");
}

/// const member functions prove, with the object as a parameter this by value, bare field names in their contracts, a call of a
/// member function inside another and from a free function, and a private field, decision 0089 steps 1 and 2.
#[test]
fn const_member_functions_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-method.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A member function with a ref-qualifier, a static member function, and a contract name that is no parameter and no field, are each
/// refused at their lines, and the rest of the struct still translates, decision 0089.
#[test]
fn member_functions_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-method-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-method-refuse.cpp:7: CXXMethodDecl: the translator has no rule for it yet.",
        "model-method-refuse.cpp:12: CXXMethodDecl: the translator has no rule for it yet.",
        "model-method-refuse.cpp:16: m_ in the contract is no parameter.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 3, "{text}");
}

/// A pure const member function is also a Dafny function. A contract calls valid() inside its struct and c.valid() and c.next()
/// outside it, and a caller of the method knows the value of the function, decision 0090.
#[test]
fn pure_member_functions_are_functions_that_contracts_call() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A contract that calls a member function that is not pure, or a name that is no member function, is refused at its line,
/// decision 0090. So is one that calls a member whose own contract is refused, decision 0095.
#[test]
fn a_contract_that_calls_a_member_function_that_is_not_pure_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-pure-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-pure-refuse.cpp:13: copy is no pure function. A contract calls a function with one return and no write.",
        "model-pure-refuse.cpp:18: three is no pure function. A contract calls a function with one return and no write.",
        "model-pure-refuse.cpp:26: nosuch in the contract is no parameter.",
        "model-pure-refuse.cpp:32: refused is no pure function. A contract calls a function with one return and no write.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 4, "{text}");
}

/// An integer argument of a member function in a contract passes as the type of its parameter, from a parameter and from result,
/// decision 0095.
#[test]
fn the_arguments_of_a_member_function_in_a_contract_pass_as_its_parameter_types() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure-args.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A contract that calls a member function outside its requires lines is named at the contract line, with the requires line that
/// may not hold, decision 0095.
#[test]
fn prove_names_a_contract_call_outside_the_requires_of_a_member_function() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pure-args-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let head = "model-pure-args-wrong.cpp:14: a requires line of the member function may not hold here.";
    assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(head)), "{head}: {text}");
    assert!(under(&text, head).iter().any(|l| l.ends_with("model-pure-args-wrong.cpp:7: requires n_ < 1000")), "{text}");
}

/// A constructor with only a member init list proves its contract, which names fields and valid() of the value it builds, and a
/// caller that builds a value, in a local and in a return, knows it, decision 0094.
#[test]
fn a_constructor_gives_the_value_it_builds() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ctor.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A constructor whose body writes a field, one that leaves a field out, a delegating constructor, and one whose init list reads a
/// field are refused at their lines, decisions 0094 and 0179.
#[test]
fn constructors_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-ctor-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let field = "model-ctor-refuse.cpp:9: a field in the body of a constructor: the translator has no rule for it yet.";
    assert!(refusals.iter().any(|l| l.ends_with(field)), "{field}: {text}");
    for line in [12, 14, 22] {
        let want = format!("model-ctor-refuse.cpp:{line}: CXXConstructorDecl: the translator has no rule for it yet.");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 4, "{text}");
}

/// A member function that writes its object proves: a field write, compound assignment, a setter that also gives a value, old() in
/// an ensures line, calls on a local that write it back, compound assignment of a local, and a void free function, decision 0096.
#[test]
fn member_functions_that_write_their_object_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-mut.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A field write that may overflow, and an ensures line that does not hold when a void function ends, are named at their lines.
/// The end of a void function is named at the line of the function, decision 0096.
#[test]
fn prove_names_a_write_that_may_overflow_and_an_ensures_line_of_a_void_function() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-mut-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-mut-wrong.cpp:8: the value may not fit int32_t.", "model-mut-wrong.cpp:12: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A call that writes a parameter, a call that writes a field of a local, old() outside the ensures lines of a function that writes
/// its object, a return of a void call, a call alone whose value is dropped, and a write to an optional field, are refused at their
/// lines, decisions 0096 and 0097.
#[test]
fn writes_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-mut-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-mut-refuse.cpp:17: c is a parameter. The translator writes only a local or a reference parameter.",
        "model-mut-refuse.cpp:23: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
        "model-mut-refuse.cpp:27: the contract line has a form the translator cannot read.",
        "model-mut-refuse.cpp:37: ReturnStmt: the translator has no rule for it yet.",
        "model-mut-refuse.cpp:45: a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.",
        "model-mut-refuse.cpp:53: CXXOperatorCallExpr: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
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

/// The conditional operator in code and in contracts, and a struct with an operator() called in code and in a contract, prove,
/// decision 0098.
#[test]
fn conditionals_and_functors_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-cond.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An ensures line that a conditional does not meet, and a branch that may overflow, are named at their lines, decision 0098.
#[test]
fn prove_names_a_conditional_that_does_not_meet_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-cond-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-cond-wrong.cpp:6: the ensures line may not hold on this return.", "model-cond-wrong.cpp:10: the value may not fit int32_t."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A contract that calls a functor whose operator() is not pure, and a call of a name that a quantifier binds, are refused at
/// their lines, decisions 0098 and 0100. A call in a branch of a conditional in a return has a model, decision 0177.
#[test]
fn conditionals_and_functors_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-cond-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-cond-refuse.cpp:11: operator() is no pure function. A contract calls a function with one return and no write.",
        "model-cond-refuse.cpp:24: the contract line has a form the translator cannot read.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// Assert lines, apply lines that call lemmas of the companion file, and a loop contract that names a field of the object in a
/// member function that writes it, prove, decision 0099.
#[test]
fn assert_and_apply_lines_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-assert.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An assert line that may not hold, and an apply line whose lemma has a requires line that may not hold, are named at their
/// lines, decision 0099.
#[test]
fn prove_names_an_assert_line_and_an_apply_line_that_may_not_hold() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-assert-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-assert-wrong.cpp:4: the assert line may not hold.", "model-assert-wrong.cpp:9: a requires line of the callee may not hold."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// An assert line that names result, an apply line of a name that is no lemma of the companion file, an assert line below the
/// last statement of its block (also where `} else if` follows), and a name that is not yet in scope, are refused at their
/// lines, decisions 0099 and 0101.
#[test]
fn assert_and_apply_lines_with_no_rule_are_refused_at_their_lines() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-assert-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-assert-refuse.cpp:5: the contract line has a form the translator cannot read.",
        "model-assert-refuse.cpp:10: Missing is no lemma of the companion file.",
        "model-assert-refuse.cpp:17: an assert or apply line needs a statement below it in its block.",
        "model-assert-refuse.cpp:21: Twice is no lemma of the companion file.",
        "model-assert-refuse.cpp:29: an assert or apply line needs a statement below it in its block.",
        "model-assert-refuse.cpp:37: y in the assert line is no variable.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 6, "{text}");
}

/// A lemma with no body in the companion file is an axiom, so prove refuses the file and never says proved, decision 0099.
#[test]
fn prove_refuses_a_lemma_with_no_body_in_the_companion_file() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-lemma.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-lemma.spec.dfy:2: a lemma with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A forall statement with no body in a lemma of the companion file is an axiom, so prove refuses it at its line and never says
/// proved, decision 0101.
#[test]
fn prove_refuses_a_forall_statement_with_no_body_in_the_companion_file() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-spec-forall.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let want = "model-spec-forall.spec.dfy:11: a forall statement with no body is an axiom.";
    assert!(text.lines().any(|l| l.starts_with("Not provable: ") && l.ends_with(want)), "{want}: {text}");
    assert!(!text.contains("ok: proved"), "{text}");
}

/// A trusted function is a method with its contract and no body. Its callers prove from the contract, and prove names each
/// trusted function with its reason before the verdict, decision 0102.
#[test]
fn trusted_functions_are_contracts_that_prove_names() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-trusted.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let trusted: Vec<&str> = text.lines().filter(|l| l.starts_with("Trusted: ")).collect();
    for want in [
        "model-trusted.cpp:7: read_status: reads a hardware status register",
        "model-trusted.cpp:18: increment: a body that the translator has no rule for",
    ] {
        assert!(trusted.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(trusted.len(), 2, "{text}");
    // Only the attribute {:axiom} tells Dafny that a method with no body is meant to have none, decision 0102.
    let dir = tempfile::tempdir().unwrap();
    let (_, out) = model("model-trusted.cpp", dir.path());
    let dfy = std::fs::read_to_string(&out).unwrap();
    assert!(dfy.contains("method {:axiom} c_read_status("), "{dfy}");
    assert!(dfy.contains("method {:axiom} c_increment("), "{dfy}");
    assert!(!dfy.contains("method {:axiom} c_headroom("), "{dfy}");
}

/// A caller that needs more than the contract of a trusted function, or that misses its requires line, is not proved. The
/// Trusted: lines come first, before each refusal and each failure, decisions 0102 and 0103.
#[test]
fn prove_names_a_caller_that_needs_more_than_a_trusted_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-trusted-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-trusted-wrong.cpp:12: the ensures line may not hold on this return.", "model-trusted-wrong.cpp:21: a requires line of the callee may not hold."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
    let lines: Vec<&str> = text.lines().collect();
    let trusted: Vec<usize> = (0..lines.len()).filter(|&i| lines[i].starts_with("Trusted: ")).collect();
    let first_fault = (0..lines.len()).find(|&i| lines[i].starts_with("Not provable: ") || lines[i].starts_with("Not proved: ")).unwrap();
    assert_eq!(trusted.len(), 2, "{text}");
    assert!(trusted.iter().all(|&i| i < first_fault), "{text}");
    assert!(lines.iter().any(|l| l.ends_with("model-trusted-wrong.cpp:7: read_status: reads a hardware status register")), "{text}");
    assert!(lines.iter().any(|l| l.ends_with("model-trusted-wrong.cpp:26: BinaryOperator <<: the translator has no rule for it yet.")), "{text}");
}

/// The //@ lines in the body of a trusted definition belong to it and are not read, and the Trusted: line names the marked
/// declaration, decision 0103.
#[test]
fn a_trusted_definition_keeps_the_lines_of_its_body_and_names_its_marked_declaration() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-trusted-body.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let trusted: Vec<&str> = text.lines().filter(|l| l.starts_with("Trusted: ")).collect();
    assert_eq!(trusted.len(), 1, "{text}");
    assert!(trusted[0].ends_with("model-trusted-body.cpp:9: count: counts with a loop"), "{text}");
}

/// A function with no body and no marker has no method, so a call of it is refused at its line, decision 0102.
#[test]
fn a_call_of_a_function_with_no_body_and_no_marker_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-trusted-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let want = "model-trusted-refuse.cpp:8: a call to read_status, which has no model in view.";
    assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    assert_eq!(refusals.len(), 1, "{text}");
}

/// A call inside an expression runs before its statement, so a nested call, a call in an operand, a call in a condition, in an
/// else-if condition, in the start and the step of a for loop, and a constructor call prove, decisions 0104 and 0105.
#[test]
fn calls_inside_expressions_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-lift.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A call before its statement keeps the requires lines of its callee, a constructor too, and its value is the value of the
/// callee, decisions 0104 and 0105.
#[test]
fn prove_names_a_call_inside_an_expression_that_does_not_meet_a_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-lift-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-lift-wrong.cpp:10: a requires line of the callee may not hold.",
        "model-lift-wrong.cpp:16: the ensures line may not hold on this return.",
        "model-lift-wrong.cpp:28: a requires line of the callee may not hold.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 3, "{text}");
}

/// A call in a while or for condition is refused at its line: C++ runs it again at each turn, decisions 0104 and 0105. A call on
/// the right of && or || or in a branch of ?: in a return has a model, decision 0177.
#[test]
fn a_call_that_cpp_may_not_run_once_is_refused_at_its_line() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-lift-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let place = "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.";
    for line in [18, 30] {
        let want = format!("model-lift-refuse.cpp:{line}: {place}");
        assert!(refusals.iter().any(|l| l.ends_with(&want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// int8_t, int16_t and uint16_t, a right shift of an unsigned and of a negative signed value, a named constexpr constant in code
/// and in a contract, and a character in a contract, prove, decision 0106. Each constant has its true value, decision 0107.
#[test]
fn small_forms_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A narrowing to int8_t that may not fit, a shift whose amount may be negative or too wide, and a contract that a constant does
/// not meet, are named at their lines, decisions 0106 and 0107.
#[test]
fn prove_names_a_narrowing_and_a_shift_that_may_fail() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    let shift = "the shift amount may be negative or not below the width of the type.";
    let mut wants = vec!["model-small-wrong.cpp:4: the value may not fit int8_t.".to_string()];
    wants.extend([8, 14].map(|line| format!("model-small-wrong.cpp:{line}: {shift}")));
    // Each wrong value of a constant, and the field that hides a constant of the file, decision 0107.
    wants.extend([25, 30, 35, 40, 50].map(|line| format!("model-small-wrong.cpp:{line}: the ensures line may not hold on this return.")));
    for want in &wants {
        assert!(failed.iter().any(|l| l.ends_with(want.as_str())), "{want}: {text}");
    }
    assert_eq!(failed.len(), wants.len(), "{text}");
}

/// A static member, a namespace constant, an unnamed namespace and a local constant of an enclosing function hide a constant of the
/// file with the same name, and so does a name with two meanings. The name in the contract is no constant then, decision 0107.
#[test]
fn a_constant_that_cpp_does_not_find_from_the_function_is_no_constant() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-small-hidden.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let wants = [
        "model-small-hidden.cpp:14: kScale in the contract is no parameter.",
        "model-small-hidden.cpp:22: k in the contract is no parameter.",
        "model-small-hidden.cpp:32: j in the contract is no parameter.",
        "model-small-hidden.cpp:44: k in the contract is no parameter.",
        "model-small-hidden.cpp:56: m in the contract is no parameter.",
        "model-small-hidden.cpp:66: n in the contract is no parameter.",
    ];
    for want in wants {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), wants.len(), "{text}");
}

/// A variable that is not constexpr is no constant of a contract, and a left shift has no rule, decision 0106.
#[test]
fn a_variable_in_a_contract_and_a_left_shift_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-small-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in ["model-small-refuse.cpp:6: scale in the contract is no parameter.", "model-small-refuse.cpp:12: BinaryOperator <<: the translator has no rule for it yet."] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 2, "{text}");
}

/// A reference parameter on the modifies line takes a value in and gives it back. A caller writes back a local or its own
/// reference parameter, and a trusted function can write one, decision 0108.
#[test]
fn reference_parameters_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// An ensures line about a reference parameter that the body does not meet, a call that does not meet a requires line, and a caller
/// that reads a local as it was before a call that wrote it, are named at their lines, decision 0108.
#[test]
fn prove_names_a_reference_parameter_that_does_not_meet_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in [
        "model-ref-wrong.cpp:6: the ensures line may not hold on this return.",
        "model-ref-wrong.cpp:19: a requires line of the callee may not hold.",
        "model-ref-wrong.cpp:33: the ensures line may not hold on this return.",
        "model-ref-wrong.cpp:40: the ensures line may not hold on this return.",
    ] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 4, "{text}");
}

/// A name on the modifies line that is no reference parameter, a reference parameter that the line does not name, and a call that
/// writes back to a parameter by value or to a field, are refused at their lines, decision 0108. A modifies line of another form is
/// refused first, and a name with parts is a name, decision 0110.
#[test]
fn a_modifies_line_and_a_write_back_with_no_rule_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-ref-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    for want in [
        "model-ref-refuse.cpp:10: n on the modifies line is no reference parameter.",
        "model-ref-refuse.cpp:15: x is a reference parameter that the modifies line does not name.",
        "model-ref-refuse.cpp:25: y is a parameter. The translator writes only a local or a reference parameter.",
        "model-ref-refuse.cpp:30: the call writes a value back, and the translator writes back only to a local or a reference parameter.",
        "model-ref-refuse.cpp:35: the contract line has a form the translator cannot read.",
        "model-ref-refuse.cpp:40: Tally::count_ on the modifies line is no reference parameter.",
        "model-ref-refuse.cpp:48: BinaryOperator <<=: the translator has no rule for it yet.",
    ] {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), 7, "{text}");
}

/// A function whose body is refused keeps a header with the values it gives back, so Dafny resolves each call of it, decision 0108.
#[test]
fn a_caller_of_a_refused_function_that_writes_a_reference_resolves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-ref-refuse.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    assert!(!text.lines().any(|l| l.starts_with("Not proved: ")), "{text}");
}

/// An enum class is a datatype, and a switch over it is a match: a case that returns, a case that ends with a break, a nested switch,
/// an enum in a struct and in a contract, decision 0109. An enum named only by its enumerators, a switch through a const reference,
/// and case bodies in braces, decision 0114.
#[test]
fn enums_and_switches_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-enum.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A case that does not meet the contract, and a value of an enum that a branch may not change, are named at their lines, decision
/// 0109.
#[test]
fn prove_names_a_switch_that_does_not_meet_its_contract() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-enum-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).collect();
    for want in ["model-enum-wrong.cpp:12: the ensures line may not hold on this return.", "model-enum-wrong.cpp:23: the ensures line may not hold on this return."] {
        assert!(failed.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(failed.len(), 2, "{text}");
}

/// A marked fall, a default, a break in another place, an enum with values written, a cast of an enum and an order of enums are
/// refused at their lines, decision 0109. So are an order of enums in a contract, an enumerator of two enums with one plain name,
/// and an enumerator whose name Dafny cannot read, decision 0114.
#[test]
fn switches_and_enums_with_no_rule_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-enum-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    let wants = [
        "model-enum-refuse.cpp:14: AttributedStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:27: DefaultStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:36: BreakStmt: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:47: Flag: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:52: CXXStaticCastExpr IntegralCast: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:56: BinaryOperator <: the translator has no rule for it yet.",
        "model-enum-refuse.cpp:60: the contract line has a form the translator cannot read.",
        "model-enum-refuse.cpp:73: the contract line has a form the translator cannot read.",
        "model-enum-refuse.cpp:79: P$: a name with a character Dafny cannot read.",
    ];
    for want in wants {
        assert!(refusals.iter().any(|l| l.ends_with(want)), "{want}: {text}");
    }
    assert_eq!(refusals.len(), wants.len(), "{text}");
}

/// A std::byte that the file declares itself is no view as bytes, so a read through it is a pun, decision 0117. Only the std::byte of
/// the system header is exempt from the row type_punning.
#[test]
fn a_byte_that_the_file_declares_is_no_view_as_bytes() {
    if !clang_tidy_available() {
        return;
    }
    let f = fixture("punning-own-byte.cpp");
    let plugin = plugin();
    let o = cplusp(&["gate", "--json", "--plugin", plugin.to_str().unwrap(), f.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let reported: BTreeSet<(String, usize)> = out.lines().map(|l| (field(l, "rule"), field(l, "line").parse::<usize>().unwrap())).collect();
    let expected: BTreeSet<(String, usize)> = [("type_punning".to_string(), 12)].into_iter().collect();
    assert_eq!(reported, expected, "{out}");
}

/// A raw copy tells the bot why the gate refuses it, decision 0120. The sentence of the plugin follows the message of the row.
#[test]
fn a_raw_copy_says_why_it_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let banned = root().join("rules/type_punning/banned.cpp");
    let o = gated(&[banned.to_str().unwrap(), "--", "-std=c++23", "-ffp-contract=off"]);
    let out = stdout(&o);
    let wants = [
        (154, "The copy reads padding into a type that is not bytes."),
        (162, "The copy writes a type that holds a pointer, a reference, an enum or a bool."),
        (194, "The copy writes to a place of unknown type."),
        (260, "The copy writes to a place of unknown type."),
        (276, "The copy writes a type that holds a pointer, a reference, an enum or a bool."),
        (297, "The copy reads a place of unknown type into a type that is not bytes."),
        (324, "The copy writes to a place of unknown type."),
        (331, "The copy writes to a place of unknown type."),
    ];
    for (line, want) in wants {
        let at = format!("banned.cpp:{line}: ");
        assert!(out.lines().any(|l| l.contains(&at) && l.ends_with(&format!("Use std::bit_cast for the bits of a value, or a pointer to bytes. {want}"))), "{line}: {out}");
    }
}

/// A refused character that the eye cannot see is named by its code point, decision 0125. The sentence for a no-break space is
/// not a quoted space.
#[test]
fn an_invisible_character_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-invisible.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 1, "{text}");
    assert!(refusals[0].ends_with("model-invisible.cpp:4: U+00A0 in a contract: the translator has no rule for it yet."), "{text}");
}

/// A format character, such as a zero-width space or a right-to-left override, is named by its code point too, decision 0126.
#[test]
fn a_format_character_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-format-char.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 2, "{text}");
    assert!(refusals[0].ends_with("model-format-char.cpp:4: U+200B in a contract: the translator has no rule for it yet."), "{text}");
    assert!(refusals[1].ends_with("model-format-char.cpp:9: U+202E in a contract: the translator has no rule for it yet."), "{text}");
}

/// A Hangul filler is a letter that prints as nothing, so it is named by its code point too, decision 0126.
#[test]
fn a_hangul_filler_in_a_contract_is_named_by_its_code_point() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-filler.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(refusals.len(), 1, "{text}");
    assert!(refusals[0].ends_with("model-filler.cpp:4: U+3164 in a contract: the translator has no rule for it yet."), "{text}");
}

/// A chain of three comparisons means each of them, and `*o` reads an optional, decision 0131. The ensures lines need the last
/// comparison of each chain, and the first and the last index of the sorted form.
#[test]
fn a_longer_chain_and_the_star_of_an_optional_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-chain.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// The chain gives no more than it says, and `*result` with no test of has_value does not prove, decision 0131.
#[test]
fn a_longer_chain_gives_no_more_and_the_star_needs_a_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-chain-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-chain-wrong.cpp:8: the ensures line may not hold on this return.", "model-chain-wrong.cpp:12: the optional may be empty or the pointer may be null here."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A chain with two directions anywhere in it, and `*` on a value that is not an optional, are refused, decision 0131.
#[test]
fn a_chain_that_turns_and_the_star_of_a_scalar_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-chain-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).collect();
    assert_eq!(
        refusals.iter().map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["4: the contract line has a form the translator cannot read.", "10: the contract line has a form the translator cannot read."],
        "{text}"
    );
}

/// A const std::array is a read-only sequence of fixed length, decision 0132: by reference and by value.
#[test]
fn a_const_array_is_a_sequence_of_fixed_length() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-array.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-array-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["8: the index may be out of range."],
        "{text}"
    );
}

/// An array with no const, a struct with an array field, and an array of bool stay out of the subset, decisions 0132 and 0136.
#[test]
fn an_array_with_no_const_and_an_array_field_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-array-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec![
            "6: std::array<int32_t, 4> &: the translator has no rule for it yet.",
            "18: Pair: the translator has no rule for it yet.",
            "23: an optional of a struct or a sequence of bool has no rule yet.",
        ],
        "{text}"
    );
}

/// has_value, value and the star read the optional that a call gives, decision 0133. A read of a value that may be missing does
/// not prove.
#[test]
fn an_optional_that_a_call_gives_is_read_through_its_temporary() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-temp-opt.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-temp-opt-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["15: the optional may be empty or the pointer may be null here."],
        "{text}"
    );
}

/// An optional of a plain struct, and `->` in code and in a contract, decision 0137.
#[test]
fn an_optional_of_a_struct_and_the_arrow_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-opt-struct.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A read through `->` of an optional that may be empty does not prove, in code and in a contract, decision 0137.
#[test]
fn the_arrow_needs_a_value() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-opt-struct-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-opt-struct-wrong.cpp:20: the optional may be empty or the pointer may be null here.", "model-opt-struct-wrong.cpp:23: the optional may be empty or the pointer may be null here."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// An optional of a struct that holds a sequence stays out, decision 0137.
#[test]
fn an_optional_of_a_struct_that_holds_a_sequence_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-opt-struct-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["11: a struct that holds a sequence is in the subset only as a parameter that the function does not write."],
        "{text}"
    );
}

/// int8_t, int16_t and uint16_t fields of a plain struct, decision 0138. A value that may not fit the field does not prove.
#[test]
fn small_integer_types_can_be_fields() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-small-fields.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-small-fields-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["10: the value may not fit uint16_t."],
        "{text}"
    );
}

/// `at` of a read-only sequence is an index, decision 0139. An index that may be out of range does not prove.
#[test]
fn at_is_an_index() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-at.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-at-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["7: the index may be out of range."],
        "{text}"
    );
}

/// A pointer to const is an optional, decision 0140: `*p`, `p->f`, `p == nullptr` and `p != nullptr`, in code and in a contract, and
/// the arguments `&x`, `nullptr` and a pointer parameter.
#[test]
fn a_pointer_to_const_is_an_optional() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pointer.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// A read through a pointer that may be null does not prove, in code and in a contract, and a caller must meet `p != nullptr`,
/// decision 0140.
#[test]
fn a_pointer_that_may_be_null_does_not_prove() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-pointer-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in [
        "model-pointer-wrong.cpp:5: the optional may be empty or the pointer may be null here.",
        "model-pointer-wrong.cpp:8: the optional may be empty or the pointer may be null here.",
        "model-pointer-wrong.cpp:19: a requires line of the callee may not hold.",
    ] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// A pointer with no const, and a pointer tested as a bool, have no rule yet, decision 0140. Two pointers do not compare, in code
/// and in a contract, and neither does `this`, decision 0141. No refusal speaks in the words of Dafny.
#[test]
fn a_pointer_with_no_const_and_a_pointer_as_a_bool_are_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-pointer-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 6, "{text}");
    assert_eq!(refusals[0], "5: int32_t *: the translator has no rule for it yet.", "{text}");
    for (i, line) in [(1, "10: "), (2, "18: "), (5, "34: ")] {
        assert!(refusals[i].starts_with(line) && refusals[i].ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
    assert_eq!(refusals[3], "21: the contract line has a form the translator cannot read.", "{text}");
    assert_eq!(refusals[4], "26: the contract line has a form the translator cannot read.", "{text}");
}

/// A unique_ptr that the code only reads is an optional, decision 0142: a const reference parameter, a result, a local that a call
/// sets, std::make_unique, `*p`, `p->f` and the test against nullptr.
#[test]
fn a_unique_ptr_that_is_only_read_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-unique.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-unique-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect::<Vec<_>>(),
        vec!["12: the optional may be empty or the pointer may be null here."],
        "{text}"
    );
}

/// A write through a unique_ptr, a move, a unique_ptr by value or by reference with no const, and two unique_ptrs compared, have no
/// rule, decision 0142.
#[test]
fn a_unique_ptr_that_is_written_or_compared_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-unique-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    assert!(!text.contains("Dafny says"), "{text}");
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 4, "{text}");
    for (r, line) in refusals.iter().zip(["8: ", "12: ", "17: ", "22: "]) {
        assert!(r.starts_with(line) && r.ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
}

/// A range-for is a loop over indexes, and an index line names the index, decision 0143. A loop with no index line proves too.
#[test]
fn a_range_for_is_a_loop_over_indexes() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-range.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-range-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    for want in ["model-range-wrong.cpp:10: the invariant may not hold when the loop starts.", "model-range-wrong.cpp:22: the value may not fit int32_t."] {
        assert!(text.lines().any(|l| l.starts_with("Not proved: ") && l.ends_with(want)), "{want}: {text}");
    }
}

/// An index line above another loop or above a function, an index name that the function has, and an index line with two names,
/// are refused, decision 0143. So are an index named as a field or a constant, and a structured binding, decision 0144.
#[test]
fn an_index_line_in_the_wrong_place_or_with_a_used_name_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-range-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let wrong_place = "a contract line in the wrong place. A requires, an ensures, a modifies or a decreases line goes above a function. An invariant or a decreases line goes above a loop, and an index line above a range-for.";
    assert_eq!(
        text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1.to_string()).collect::<Vec<_>>(),
        vec![
            format!("8: {wrong_place}"),
            "17: i on the index line is a name the function already has.".to_string(),
            "26: the contract line has a form the translator cannot read.".to_string(),
            format!("33: {wrong_place}"),
            "43: count on the index line is a name the function already has.".to_string(),
            "55: N on the index line is a name the function already has.".to_string(),
            "70: CXXForRangeStmt: the translator has no rule for it yet.".to_string(),
        ],
        "{text}"
    );
}

/// A vector by reference that the function writes takes its value in and gives it back, decision 0145: element writes, reads,
/// and a loop that writes each element.
#[test]
fn a_vector_by_reference_that_the_function_writes_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-ref.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-ref-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 2, "{text}");
    assert_eq!(failed[0], "8: the index may be out of range.", "{text}");
    assert!(failed[1].ends_with(": the ensures line may not hold on this return."), "{text}");
}

/// A vector by reference that the modifies line does not name, clear, a compound write, a vector of bool and a call that
/// passes the vector on are refused, decisions 0145, 0147 and 0148.
#[test]
fn a_vector_by_reference_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-vec-ref-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(refusals.len(), 5, "{text}");
    assert_eq!(refusals[0], "7: v is a reference parameter that the modifies line does not name.", "{text}");
    for (r, line) in refusals[1..4].iter().zip(["12: ", "18: ", "22: "]) {
        assert!(r.starts_with(line) && r.ends_with(": the translator has no rule for it yet."), "{line}: {text}");
    }
    // The call passes the vector on, decision 0147.
    assert_eq!(refusals[4], "34: v is a vector by reference. A call that passes it on has no rule yet.", "{text}");
}

/// push_back adds one element at the end of a vector by reference, and Dafny checks each index and the length after, decision
/// 0148.
#[test]
fn push_back_grows_a_vector_by_reference() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-vec-push.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-vec-push-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 2, "{text}");
    assert_eq!(failed[0], "10: the index may be out of range.", "{text}");
    assert!(failed[1].ends_with(": the ensures line may not hold on this return."), "{text}");
}

/// The example sorted_insert proves with push_back, its loop invariants and its companion file, decision 0148.
#[test]
fn the_sorted_insert_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/sorted_insert/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

/// count_if with a lambda written in the call proves against a companion count that says the same test, decision 0149. A lambda
/// with another test fails its ensures line, and a count with no bound fails the int64 fit and the int32 fit at line 14.
#[test]
fn count_if_with_a_lambda_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("model-count-if.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
    let o = prove("model-count-if-wrong.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed.len(), 3, "{text}");
    assert!(failed[0].starts_with("9: ") && failed[0].ends_with(": the ensures line may not hold on this return."), "{text}");
    assert_eq!(failed[1], "14: the value may not fit int64_t.", "{text}");
    assert_eq!(failed[2], "14: the value may not fit int32_t.", "{text}");
}

/// Another algorithm, an init capture and a lambda body of two statements are refused at their lines, and the lambda is no
/// function of its own, decision 0149.
#[test]
fn count_if_with_no_rule_is_refused() {
    if !clang_tidy_available() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let (o, _) = model("model-count-if-refuse.cpp", dir.path());
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(1), "stdout: {text} stderr: {}", stderr(&o));
    let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    let mut lines: Vec<&str> = refusals.iter().map(|r| r.split(':').next().unwrap()).collect();
    lines.dedup();
    assert_eq!(lines, ["7", "11", "15", "22", "26"], "{text}");
    assert!(!text.contains("CXXMethodDecl"), "{text}");
    // A count_if that misses the rule names the limit that it misses, and only that, decision 0157.
    let no_rule = ": the translator has no rule for it yet.";
    for (line, what) in [
        ("11", "count_if with an init capture in its lambda"),
        ("15", "count_if with a lambda whose body is more than one return"),
        ("22", "count_if over a range other than v.begin(), v.end() of one sequence parameter"),
        ("26", "count_if with a lambda whose parameter is not the element type"),
    ] {
        let at: Vec<&&str> = refusals.iter().filter(|r| r.split(':').next() == Some(line)).collect();
        assert_eq!(at, [&format!("{line}: {what}{no_rule}").as_str()], "{line}: {text}");
    }
}

/// The example lambdas proves with count_if and its companion file, decision 0149.
#[test]
fn the_lambdas_example_proves() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
    let o = prove("../../../../examples/lambdas/example.cpp", &[], &dafny);
    let text = stdout(&o);
    assert_eq!(o.status.code(), Some(0), "stdout: {text} stderr: {}", stderr(&o));
    assert_eq!(text.lines().last(), Some("ok: proved"), "{text}");
}

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

const AXIOM: &str = "Axiom: Double.dfy: RoundError: IEEE 754 binary64, round to nearest even, gradual underflow, one rounding per operation.";

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
        let refusals: Vec<&str> = text.lines().filter(|l| l.starts_with("Not provable: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
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
    assert_eq!(failed, ["6: the integer may be too large for an exact double.", "11: the ensures line may not hold on this return."], "{text}");
    // A conversion alone names its own axiom and not the one of the operations.
    assert!(text.contains(exact) && !text.contains(AXIOM), "{text}");
}

/// A local vector is a copy: a write to the copy leaves the vector of the caller as it was, and a write to the vector after the copy
/// leaves the copy as it was, decision 0160. A contract that reads the copy as the vector, or the vector as a view, fails.
#[test]
fn a_local_vector_is_a_copy() {
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
    assert_eq!(failed, ["10: the ensures line may not hold on this return.", "20: the ensures line may not hold on this return."], "{text}");
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
    assert_eq!(
        refusals,
        [format!("15: {copy}")],
        "{text}"
    );
}

const SORT_AXIOM: &str = "Axiom: Algorithm.dfy: StdSort: std::sort with a strict weak order gives a permutation of its range, and no later element compares less than an earlier one, C++23 [sort] and [alg.sorting.general].";

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
    assert_eq!(failed, ["11: the ensures line may not hold on this return.", "19: the ensures line may not hold on this return."], "{text}");
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
    let named = blocks(&stdout(&o))
        .into_iter()
        .any(|(h, under)| h.ends_with("the ensures line may not hold on this return.") && under.iter().any(|u| u.ends_with("model-companion-fail.spec.dfy:2: ensures x > 0")));
    assert!(named, "{}", stdout(&o));
}

/// The blocks of `Not proved` lines: each head with the lines under it.
fn blocks(text: &str) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    for l in text.lines() {
        if l.starts_with("Not proved: ") {
            out.push((l.to_string(), Vec::new()));
        } else if l.starts_with("  ") {
            if let Some(last) = out.last_mut() {
                last.1.push(l.to_string());
            }
        }
    }
    out
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
        found.iter().filter(|(h, under)| h.ends_with(head) && under.iter().any(|u| u.starts_with("  The contract line: ") && u.ends_with(clause))).count()
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
    let index = text.lines().filter(|l| l.starts_with("Not proved: ") && l.ends_with("model-two-index.cpp:9: the index may be out of range.")).count();
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
    assert!(refusals[1].starts_with("12: ") && refusals[1].contains("FloatingToIntegral") && refusals[1].ends_with(": the translator has no rule for it yet."), "{text}");
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
    let lines: BTreeSet<&str> = text.lines().filter(|l| l.contains("`operator[]` with a variable index")).filter_map(|l| l.split("variable-index-ban.cpp:").nth(1)).filter_map(|r| r.split(':').next()).collect();
    // An explicit `operator[]` call and a C array by reference too, which the upstream check misses.
    assert_eq!(lines, BTreeSet::from(["8", "12", "16", "24", "28"]), "{text}");
}

const SHAPE_AXIOM: &str = "Axiom: model: Shape: a call through Shape runs an override that keeps the contract of Shape, C++23 [class.virtual]. Each override of Shape in this file is checked against that contract.";

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
            "43: Sound has two virtual functions of one name. The translator has no rule for it yet.",
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
            "21: a pure virtual function that gives no value: the translator has no rule for it yet.",
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

/// Two moves of one local in one statement, a move and a read of one local in one call, a move of a parameter in a call, a move in a
/// condition, a move of an element of a vector, a move into std::make_unique at a parameter by const reference, and a call that
/// writes through a field have no rule, so no two names share one object and no read sees a moved local, decision 0171.
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
            "48: p is a parameter. The translator writes only a local or a reference parameter.",
            "54: a std::move of a std::unique_ptr has a rule only in a call that stands alone, the start value of a local or a return.",
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

/// An override whose body writes a local, or calls a member function of its own class, has no function in the model, so its class
/// is refused, decision 0172.
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

/// A global that a function lists is an implicit parameter: a reference parameter on a modifies line, a value on a reads line. A
/// call passes it on, a trusted function takes it, and a function can change only the globals it lists, decision 0173.
#[test]
fn a_global_is_an_implicit_parameter() {
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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
    let Some(dafny) = dafny() else { return };
    if !clang_tidy_available() {
        return;
    }
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

/// A vector by rvalue reference that the modifies line does not name, a vector parameter by value, `v(n)`, `v{a, b}`, and a move
/// in a return or an assignment are refused, decision 0185.
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
        "15: std::vector<int32_t>: the translator has no rule for it yet.".to_string(),
        format!("22: {local}"),
        format!("28: {local}"),
        "36: CXXConstructExpr: the translator has no rule for it yet.".to_string(),
        "44: CXXOperatorCallExpr: the translator has no rule for it yet.".to_string(),
        "50: CXXTemporaryObjectExpr: the translator has no rule for it yet.".to_string(),
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
/// callers, decision 0180.
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
        "54: Box<int>: the translator has no rule for it yet.",
        "58: Box<int32_t>: the translator has no rule for it yet.",
        "65: a function template with no instance: the translator has no rule for it yet.",
        "84: a type argument with no Dafny name: the translator has no rule for it yet.",
        "90: a call to count<std::vector<int>>, which has no model in view.",
    ];
    assert_eq!(refusals, want, "{text}");
    let failed: Vec<&str> = text.lines().filter(|l| l.starts_with("Not proved: ")).map(|l| l.rsplit_once(".cpp:").unwrap().1).collect();
    assert_eq!(failed, ["22: the ensures line may not hold on this return."], "{text}");
    assert!(!text.contains("Dafny says"), "{text}");
}

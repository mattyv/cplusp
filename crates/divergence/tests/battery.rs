//! One invariant over every case in divergence/cases: Dafny says what case.yaml says it says,
//! the witness shows what case.yaml says it shows, and the skill file carries the case's rule.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;

#[derive(Deserialize)]
struct Case {
    construct: String,
    #[allow(dead_code)]
    gap: u32,
    #[allow(dead_code)]
    cpp: String,
    #[allow(dead_code)]
    naive_does: String,
    #[allow(dead_code)]
    side: Side,
    #[allow(dead_code)]
    mitigation: String,
    naive: Verdict,
    #[serde(default)]
    naive_is_wrong: bool,
    mitigated: Verdict,
    witness: Witness,
    rule: String,
}

#[derive(Deserialize, PartialEq, Debug, Clone, Copy)]
#[serde(rename_all = "lowercase")]
enum Verdict {
    Verifies,
    Fails,
}

#[derive(Deserialize, PartialEq, Debug, Clone, Copy)]
#[serde(rename_all = "lowercase")]
enum Side {
    Model,
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
    prints: Option<String>,
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
    assert!(text.contains("verifier finished"), "{}: dafny did not finish:\n{text}", file.display());
    if text.contains(", 0 errors") { Verdict::Verifies } else { Verdict::Fails }
}

#[test]
fn every_case_says_what_it_claims() {
    let cases = root().join("divergence/cases");
    let skill = std::fs::read_to_string(root().join("skills/cplusp-dafny/SKILL.md")).unwrap();
    let out_dir = std::env::temp_dir().join(format!("cplusp-divergence-{}", std::process::id()));
    std::fs::create_dir_all(&out_dir).unwrap();
    let mut seen = 0;
    for entry in std::fs::read_dir(&cases).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        let id = dir.file_name().unwrap().to_string_lossy().into_owned();
        let case: Case = serde_yaml::from_str(&std::fs::read_to_string(dir.join("case.yaml")).unwrap()).unwrap_or_else(|e| panic!("{id}/case.yaml: {e}"));

        // Dafny verdicts.
        assert_eq!(verdict(&dir.join("naive.dfy")), case.naive, "{id}: naive.dfy ({})", case.construct);
        assert_eq!(verdict(&dir.join("mitigated.dfy")), case.mitigated, "{id}: mitigated.dfy");
        assert_eq!(case.mitigated, Verdict::Verifies, "{id}: the mitigated model must verify, or it is not a mitigation");
        if case.naive_is_wrong {
            assert_eq!(case.naive, Verdict::Verifies, "{id}: a naive model can only be wrong if Dafny accepted it");
        }

        // The witness, compiled with the sanitizer.
        let exe = out_dir.join(&id);
        let build = Command::new("clang++-18")
            .args(["-std=c++20", "-O0", "-fsanitize=undefined", "-fno-sanitize-recover=all"])
            .arg(dir.join("code.cpp"))
            .arg(dir.join("witness.cpp"))
            .arg("-o")
            .arg(&exe)
            .output()
            .expect("clang++ runs");
        assert!(build.status.success(), "{id}: witness does not build:\n{}", String::from_utf8_lossy(&build.stderr));
        let run = Command::new(&exe).output().expect("witness runs");
        let err = String::from_utf8_lossy(&run.stderr);
        let out = String::from_utf8_lossy(&run.stdout);
        if case.witness.ubsan {
            assert!(err.contains("runtime error"), "{id}: the witness should hit undefined behaviour, stderr:\n{err}");
        } else {
            assert!(!err.contains("runtime error"), "{id}: unexpected undefined behaviour:\n{err}");
        }
        if let Some(expected) = &case.witness.prints {
            assert_eq!(out.trim(), expected.trim(), "{id}: witness output");
        }

        // The rule is in the skill, word for word.
        assert!(skill.contains(&format!("## {id}")), "{id}: no section in skills/cplusp-dafny/SKILL.md");
        for line in case.rule.lines().filter(|l| !l.trim().is_empty()) {
            assert!(skill.contains(line.trim()), "{id}: rule line missing from the skill: {line}");
        }
        seen += 1;
    }
    let _ = std::fs::remove_dir_all(&out_dir);
    assert!(seen >= 1, "no cases found");
}

/// docs/mitigations.md is generated from the cases. It must match what the generator says today.
#[test]
fn the_mitigation_report_is_up_to_date() {
    let expected = divergence::report(&root().join("divergence/cases")).expect("report");
    let actual = std::fs::read_to_string(root().join("docs/mitigations.md")).expect("docs/mitigations.md exists");
    assert_eq!(actual, expected, "docs/mitigations.md is stale. Run: cargo run -p divergence > docs/mitigations.md");
}

/// The shape of the report, pinned so the docs reader can rely on it.
#[test]
fn the_mitigation_report_has_one_row_per_case_in_a_fixed_shape() {
    let report = divergence::report(&root().join("divergence/cases")).expect("report");
    let mut lines = report.lines();
    assert_eq!(lines.next().unwrap(), "# Mitigations");
    assert!(report.contains("Generated by `cargo run -p divergence` from `divergence/cases/*/case.yaml`. Do not edit by hand."), "{report}");
    assert!(report.contains("| Case | Construct | Gap | C++ does | Naive model does | Naive verdict | Mitigation | Side |"), "{report}");
    assert!(report.contains("| signed_overflow | Signed addition on int32_t | 4 |"), "{report}");
    assert!(report.contains("| verifies, wrong |"), "{report}");
    let cases = std::fs::read_dir(root().join("divergence/cases")).unwrap().filter(|e| e.as_ref().unwrap().path().is_dir()).count();
    let rows = report.lines().filter(|l| l.starts_with("| ") && !l.starts_with("| Case") && !l.starts_with("| ---")).count();
    assert_eq!(rows, cases, "one row per case");
}

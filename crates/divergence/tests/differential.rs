//! The differential run: the model compiled to a program and run beside the C++ on the same inputs. The battery proves the
//! divergences we thought of. This run looks for the ones we did not. divergence/README.md describes the command and the files.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde::Deserialize;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

fn divergence(args: &[&str]) -> (Output, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_divergence")).args(args).current_dir(root()).output().expect("divergence runs");
    let out = String::from_utf8_lossy(&o.stdout).into_owned();
    let err = String::from_utf8_lossy(&o.stderr).into_owned();
    (o, out, err)
}

#[derive(Deserialize)]
struct Case {
    #[serde(default)]
    naive_is_wrong: bool,
    differential: Option<Differential>,
}

#[derive(Deserialize)]
struct Differential {
    runs: usize,
}

/// The cases that carry a driver today. The test below runs every case that has one, so this list only keeps them from going away.
const PLANNED: &[&str] = &["signed_overflow", "signed_division", "shift", "sign_compare", "promotion_before_widening", "fold_init_type"];

#[test]
fn the_planned_cases_carry_a_driver() {
    for id in PLANNED {
        let dir = root().join("divergence/dafny/cases").join(id);
        let case: Case = serde_yaml::from_str(&std::fs::read_to_string(dir.join("case.yaml")).unwrap()).unwrap();
        assert!(case.differential.is_some(), "{id}: case.yaml has no differential block");
        assert!(dir.join("drive.dfy").exists() && dir.join("drive.cpp").exists(), "{id}: no drive.dfy and drive.cpp");
    }
}

/// Every case with a driver: the mitigated model and the C++ under the rule print the same line for every generated input.
/// And where the battery says the naive model is wrong, the naive model and the bot's C++ part ways on some input, which
/// shows the run can see what the witness saw. A run that cannot see the known fault proves nothing about unknown ones.
#[test]
fn the_model_and_the_cpp_agree_on_every_input_and_the_naive_model_does_not() {
    let cases = root().join("divergence/dafny/cases");
    let mut seen = 0;
    for entry in std::fs::read_dir(&cases).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        let id = dir.file_name().unwrap().to_string_lossy().into_owned();
        let case: Case = serde_yaml::from_str(&std::fs::read_to_string(dir.join("case.yaml")).unwrap()).unwrap();
        let Some(spec) = case.differential else { continue };
        assert!(dir.join("drive.dfy").exists() && dir.join("drive.cpp").exists(), "{id}: a differential block needs drive.dfy and drive.cpp");
        seen += 1;
        let rel = format!("divergence/dafny/cases/{id}");
        let (o, out, err) = divergence(&["differential", &rel]);
        assert_eq!(o.status.code(), Some(0), "{id}: the mitigated model and the C++ under the rule must agree. stdout: {out} stderr: {err}");
        assert_eq!(out.trim(), format!("agree: {id}, {} inputs", spec.runs), "{id}: the verdict line");
        if case.naive_is_wrong {
            let (o, out, err) = divergence(&["differential", &rel, "--naive"]);
            assert_eq!(o.status.code(), Some(1), "{id}: the naive model must part ways with the C++ on some input, or the run cannot see what the witness saw. stdout: {out} stderr: {err}");
            let first = out.lines().next().unwrap_or_default();
            assert!(
                first.starts_with(&format!("diverge: {id}, input ")) && first.contains(": C++ ") && first.contains(", model "),
                "{id}: the verdict line names the input and both outputs, got: {first}"
            );
        }
    }
    assert!(seen >= PLANNED.len(), "found {seen} cases with a differential block, planned {}", PLANNED.len());
}

/// A run the command cannot complete is an error, never a verdict.
#[test]
fn the_differential_run_refuses_a_case_without_a_driver() {
    let (o, out, err) = divergence(&["differential", "divergence/dafny/cases/const_alias"]);
    assert_eq!(o.status.code(), Some(2), "stdout: {out} stderr: {err}");
    assert!(err.contains("const_alias: no differential block in case.yaml"), "stderr: {err}");
    assert!(out.trim().is_empty(), "no verdict on an error, got: {out}");
}

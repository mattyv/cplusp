//! The command as the bot and a human run it. docs/policy.md is the reference.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod policy;
mod gate;
mod markers;
mod basics;
mod structs;
mod forms;
mod doubles;
mod interfaces;
mod names;
mod classes;

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

const AXIOM: &str = "Axiom: Double.dfy: RoundError: IEEE 754 binary64, round to nearest even, gradual underflow, one rounding per operation.";

const SORT_AXIOM: &str = "Axiom: Algorithm.dfy: StdSort: std::sort with a strict weak order gives a permutation of its range, and no later element compares less than an earlier one, C++23 [sort] and [alg.sorting.general].";

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

const SHAPE_AXIOM: &str = "Axiom: model: Shape: a call through Shape runs an override that keeps the contract of Shape, C++23 [class.virtual]. Each override of Shape in this file is checked against that contract.";

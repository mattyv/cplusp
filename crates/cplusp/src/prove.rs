//! The prover side of `cplusp prove`, decision 0068. It runs Dafny on the model, reads its errors, and names each one at the C++ line
//! it comes from. The map from Dafny lines to C++ is built by `model.rs`. Nothing here decides what is allowed.

use std::fs;
use std::process::{Command, ExitCode, Stdio};

use anyhow::{Context, Result};

use crate::model::{Line, Map, Translation};

/// Where to look for Dafny, after the env var `DAFNY`.
const INSTALLED: &str = "/opt/dafny/dafny/dafny";

/// An error of Dafny: the line of the Dafny text, the message, and the lines of its related locations.
struct Error {
    line: usize,
    message: String,
    related: Vec<usize>,
}

/// The first Dafny that runs: the env var `DAFNY`, the install path, then `dafny` on the PATH.
fn find_dafny() -> Result<String> {
    let found = std::env::var("DAFNY")
        .into_iter()
        .chain([INSTALLED.to_string(), "dafny".to_string()])
        .find(|c| Command::new(c).arg("--version").stdin(Stdio::null()).output().is_ok_and(|o| o.status.success()));
    found.with_context(|| format!("dafny not found. Set DAFNY, install it at {INSTALLED}, or put dafny on the PATH."))
}

/// The line number of `PATH(L,C): KIND: MESSAGE`, and the message, when the line has that kind.
fn at(text: &str, kind: &str) -> Option<(usize, String)> {
    let (head, message) = text.split_once(&format!(": {kind}: "))?;
    let inside = head.strip_suffix(')')?.rsplit_once('(')?.1;
    Some((inside.split_once(',')?.0.parse().ok()?, message.to_string()))
}

/// The errors in the output of Dafny. A related location belongs to the error line before it.
fn errors(output: &str) -> Vec<Error> {
    let mut found: Vec<Error> = Vec::new();
    for l in output.lines() {
        if let Some((line, message)) = at(l, "Error") {
            found.push(Error { line, message, related: Vec::new() });
        } else if let (Some((line, _)), Some(last)) = (at(l, "Related location"), found.last_mut()) {
            last.related.push(line);
        }
    }
    found
}

/// The C++ type of a Dafny type.
fn cpp_type(dafny: &str) -> Option<&'static str> {
    Some(match dafny {
        "int32" => "int32_t",
        "int64" => "int64_t",
        "uint8" => "uint8_t",
        "uint32" => "uint32_t",
        "uint64" => "uint64_t",
        _ => return None,
    })
}

/// The type between the quotes at the end of a message, as C++ writes it.
fn quoted_type(message: &str) -> Option<&'static str> {
    cpp_type(message.strip_suffix('\'')?.rsplit_once('\'')?.1)
}

fn timed_out(message: &str) -> bool {
    message.starts_with("Verification of '") && message.contains(" timed out after ")
}

/// The sentence for a message of Dafny. The words are fixed. A message with no sentence keeps the words of Dafny.
fn sentence(message: &str) -> String {
    let message = message.trim();
    let fit = |t: &str| format!("the value may not fit {t}.");
    match message {
        "a postcondition could not be proved on this return path" => "the ensures line does not hold on this return.".to_string(),
        "index out of range" => "the index may be out of range.".to_string(),
        "this loop invariant could not be proved on entry" => "the invariant may not hold when the loop starts.".to_string(),
        "this invariant could not be proved to be maintained by the loop" => "the loop may not keep the invariant.".to_string(),
        "decreases expression might not decrease" => "the decreases line may not decrease on each turn of the loop.".to_string(),
        "decreases expression must be bounded below by 0" => "the decreases line may go below zero.".to_string(),
        "a precondition for this call could not be proved" => "a requires line of the callee may not hold.".to_string(),
        m if m.starts_with("cannot prove termination") => "the prover cannot show that this ends.".to_string(),
        m if timed_out(m) => "the prover reached its time limit. The result is unknown.".to_string(),
        m if m.starts_with("result of operation might violate newtype constraint for '") || m.starts_with("value does not satisfy the subset constraints of '") => {
            quoted_type(m).map_or_else(|| format!("Dafny says: {}.", m.trim_end_matches('.')), fit)
        }
        m => format!("Dafny says: {}.", m.trim_end_matches('.')),
    }
}

/// The contract line at a place, as `FILE:LINE: WORD TEXT`.
fn contract(map: &Map, place: u32, shown: &dyn Fn(&str) -> String) -> Option<String> {
    let (word, text) = map.contracts.get(&place)?;
    let (file, line) = &map.places[place as usize];
    Some(format!("{}:{line}: {word} {text}", shown(file)))
}

/// Run Dafny on the model and print what it did not prove. Exit 0 when it proved all, 1 when not, and 2 when it cannot run or says nothing
/// that can be read. `refused` is true when the translator refused something: the proof may be complete and the file still not proved.
pub fn run(t: &Translation, limit: u32, refused: bool, shown: &dyn Fn(&str) -> String) -> Result<ExitCode> {
    let dafny = find_dafny()?;
    let tmp = tempfile::tempdir().context("cannot create a temporary directory")?;
    let file = tmp.path().join("model.dfy");
    fs::write(&file, &t.dafny).with_context(|| format!("cannot write {}", file.display()))?;
    let run = Command::new(&dafny)
        .args(["verify", "--verification-time-limit", &limit.to_string(), "--allow-warnings"])
        .arg(&file)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("cannot run {dafny}"))?;
    let output = format!("{}{}", String::from_utf8_lossy(&run.stdout), String::from_utf8_lossy(&run.stderr));
    let found = errors(&output);
    if !run.status.success() && found.is_empty() {
        eprint!("dafny failed ({}):\n{output}", run.status);
        return Ok(ExitCode::from(2));
    }
    let map = &t.map;
    let here = |line: usize| line.checked_sub(1).and_then(|n| map.lines.get(n)).and_then(Option::as_ref);
    for e in &found {
        let message = e.message.trim();
        let Some(Line { place, scope }) = here(e.line) else {
            // ponytail: an error on a line with no C++ place, such as a resolution error, is named by its Dafny line. Upgrade: map it to the function.
            println!("Not proved: model.dfy:{}: {}", e.line, sentence(message));
            continue;
        };
        let (path, line) = &map.places[*place as usize];
        println!("Not proved: {}:{line}: {}", shown(path), sentence(message));
        let mut told = vec![*place];
        for l in e.related.iter().filter_map(|r| here(*r)) {
            if !told.contains(&l.place) {
                if let Some(text) = contract(map, l.place, shown) {
                    println!("  The contract line: {text}");
                    told.push(l.place);
                }
            }
        }
        if !timed_out(message) {
            for p in scope {
                if let Some(text) = contract(map, *p, shown) {
                    println!("  It assumes: {text}");
                }
            }
        }
    }
    if found.is_empty() && !refused {
        println!("ok: proved");
        return Ok(ExitCode::SUCCESS);
    }
    Ok(ExitCode::from(1))
}

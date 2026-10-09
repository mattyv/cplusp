//! The prover side of `cplusp prove`, decision 0068. It runs Dafny on the model, reads its errors, and names each one at the C++ line
//! it comes from. The map from Dafny lines to C++ is built by `model.rs`. Nothing here decides what is allowed.

use std::fs;
use std::process::{Command, ExitCode, Stdio};

use anyhow::{Context, Result};
use cplusp_core::verdict::{verdict, Verdict};

use crate::model::{Line, Map, Translation};

/// Where to look for Dafny, after the env var `DAFNY`.
const INSTALLED: &str = "/opt/dafny/dafny/dafny";

/// Why Dafny gave no proof run: it could not resolve the file, or it could not parse it.
#[derive(PartialEq, Clone, Copy)]
enum Unread {
    Resolve,
    Parse,
}

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

/// The counts of a summary line, `Dafny program verifier finished with N verified, M errors[, K time outs]`, as verified items, errors and
/// time-outs. Dafny gives `N resolution/type errors detected in FILE` when it cannot resolve the file, and `N parse errors detected in FILE`
/// when it cannot parse it. Either line counts as N errors, and the second fact is `Some(kind)`. `run` decides whether a parse error is the
/// author's. `None` when the line is not a summary or its shape cannot be read.
fn counts(line: &str) -> Option<((u64, u64, u64), Option<Unread>)> {
    if let Some((n, rest)) = line.split_once(' ') {
        for (word, kind) in [("resolution/type error", Unread::Resolve), ("parse error", Unread::Parse)] {
            if rest.starts_with(word) && rest.contains(" detected in ") {
                return Some(((0, n.parse().ok()?, 0), Some(kind)));
            }
        }
    }
    let rest = line.strip_prefix("Dafny program verifier finished with ")?;
    let number = |part: &str, words: &[&str]| -> Option<u64> {
        let (n, w) = part.split_once(' ')?;
        words.contains(&w).then(|| n.parse().ok())?
    };
    let found = match rest.trim_end().split(", ").collect::<Vec<_>>()[..] {
        [v, e] => (number(v, &["verified"])?, number(e, &["error", "errors"])?, 0),
        [v, e, t] => (number(v, &["verified"])?, number(e, &["error", "errors"])?, number(t, &["time out", "time outs"])?),
        _ => return None,
    };
    Some((found, None))
}

/// The type between the quotes at the end of a message, as C++ writes it.
fn quoted_type(message: &str) -> Option<&'static str> {
    Some(match message.strip_suffix('\'')?.rsplit_once('\'')?.1 {
        "int32" => "int32_t",
        "int64" => "int64_t",
        "uint8" => "uint8_t",
        "uint32" => "uint32_t",
        "uint64" => "uint64_t",
        _ => return None,
    })
}

fn timed_out(message: &str) -> bool {
    message.starts_with("Verification of '") && message.contains(" timed out after ")
}

/// The sentence for a message of Dafny. The words are fixed. A message with no sentence keeps the words of Dafny.
fn sentence(message: &str) -> String {
    let message = message.trim();
    let fit = |t: &str| format!("the value may not fit {t}.");
    match message {
        "a postcondition could not be proved on this return path" => "the ensures line may not hold on this return.".to_string(),
        "destructor 'value' can only be applied to datatype values constructed by 'Some'" => "the optional may be empty here.".to_string(),
        "index out of range" => "the index may be out of range.".to_string(),
        "lower bound out of range" => "the offset may be past the end.".to_string(),
        "this loop invariant could not be proved on entry" => "the invariant may not hold when the loop starts.".to_string(),
        "this invariant could not be proved to be maintained by the loop" => "the loop may not keep the invariant.".to_string(),
        "decreases clause might not decrease" => "the decreases line may not decrease at this call.".to_string(),
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
pub fn run(t: &Translation, limit: u32, refused: bool, source: &str, shown: &dyn Fn(&str) -> String) -> Result<ExitCode> {
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
    // A warning of a declaration with no body, on a line of the companion file, is an axiom, decision 0079. Only these warnings count.
    let map = &t.map;
    let axioms: Vec<(String, usize)> = output
        .lines()
        .filter_map(|l| at(l, "Warning"))
        .filter(|(_, m)| m.contains("bodyless") || m.contains("{:axiom}"))
        .filter(|(line, _)| line.checked_sub(1).is_some_and(|n| map.companion.contains(&n)))
        .filter_map(|(line, _)| map.lines[line - 1].as_ref().map(|l| map.places[l.place as usize].clone()))
        .map(|(path, line)| (path, line as usize))
        .collect();
    // The core decides: it reads the exit status, the summary, the error lines, the refusals, the axioms and the methods together, decisions 0077 and 0080.
    let (summary, unread) = output.lines().find_map(counts).map_or((None, None), |(c, r)| (Some(c), r));
    // A line at the end of the file, one past the last line of the companion file, is the last line, decision 0083.
    let in_companion = |line: usize| {
        let last = map.companion.end;
        (!map.companion.is_empty() && (map.companion.contains(&line.wrapping_sub(1)) || line == last + 1)).then_some(line.min(last))
    };
    // A parse error is the author's only when each error is in the companion file. Else it is a failure of the tool, decision 0069.
    let summary = if unread == Some(Unread::Parse) && !(found.iter().all(|e| in_companion(e.line).is_some()) && !found.is_empty()) { None } else { summary };
    let verdict = verdict(run.status.success(), summary, found.len(), refused, axioms.len(), t.methods);
    if verdict == Verdict::ToolFailed {
        eprint!("dafny failed\n{output}");
        return Ok(ExitCode::from(2));
    }
    for (path, line) in &axioms {
        println!("Not provable: {}:{line}: a function with no body is an axiom.", shown(path));
    }
    let here = |line: usize| line.checked_sub(1).and_then(|n| map.lines.get(n)).and_then(Option::as_ref);
    for e in &found {
        let message = e.message.trim();
        // Dafny could not read the file, so no proof ran. Each error is named at its place in the words of Dafny, decision 0080.
        if unread.is_some() {
            let at = in_companion(e.line).unwrap_or(e.line);
            let (path, line) = here(at).map_or_else(|| ("model.dfy".to_string(), at as u32), |l| map.places[l.place as usize].clone());
            println!("Not provable: {}:{line}: Dafny says: {}.", shown(&path), message.trim_end_matches('.'));
            continue;
        }
        // An error on a line of the companion file has no return, call or loop of a method, so it keeps the words of Dafny, decision 0084.
        if let Some(at) = in_companion(e.line) {
            let (path, line) = here(at).map_or_else(|| ("model.dfy".to_string(), at as u32), |l| map.places[l.place as usize].clone());
            println!("Not proved: {}:{line}: Dafny says: {}.", shown(&path), message.trim_end_matches('.'));
            continue;
        }
        let Some(Line { place, scope, own }) = here(e.line) else {
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
            // The invariants of a loop do not hold yet when the loop starts.
            let own = own.iter().filter(|_| !message.starts_with("this loop invariant could not be proved on entry"));
            for p in scope.iter().chain(own) {
                if let Some(text) = contract(map, *p, shown) {
                    println!("  It assumes: {text}");
                }
            }
        }
    }
    // The count of verified items is the only fault, decision 0083.
    if let (Some((v, 0, 0)), true) = (summary, found.is_empty() && !refused && axioms.is_empty() && verdict == Verdict::NotProved) {
        println!("Not provable: {source}: Dafny verified fewer items than the model has methods: {v} for {}.", t.methods);
    }
    if verdict == Verdict::Proved {
        println!("ok: proved");
        return Ok(ExitCode::SUCCESS);
    }
    Ok(ExitCode::from(1))
}

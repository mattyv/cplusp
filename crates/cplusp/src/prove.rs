//! The prover side of `cplusp prove`, decision 0068. It runs Dafny on the model, reads its errors, and names each one at the C++ line
//! it comes from. The map from Dafny lines to C++ is built by `model.rs`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fs;
use std::process::{Command, ExitCode, Stdio};

use anyhow::{Context, Result};
use cplusp_core::dafny::{in_companion_exec, judge, read_dafny};
use cplusp_core::verdict::Verdict;

use crate::model::{Line, Map, Translation, PRELUDE};

/// Where to look for Dafny, after the env var `DAFNY`.
const INSTALLED: &str = "/opt/dafny/dafny/dafny";

/// An error of Dafny: the line of the Dafny text, the message, and the lines of its related locations.
struct Error {
    line: usize,
    /// The column of the error in the Dafny text, from its header `(LINE,COLUMN): Error: `, or none when the header is not there.
    column: Option<usize>,
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

/// The type between the quotes at the end of a message, as C++ writes it.
fn quoted_type(message: &str) -> Option<&'static str> {
    Some(match message.strip_suffix('\'')?.rsplit_once('\'')?.1 {
        "int8" => "int8_t",
        "int16" => "int16_t",
        "uint16" => "uint16_t",
        "int32" => "int32_t",
        "int64" => "int64_t",
        "uint8" => "uint8_t",
        "uint32" => "uint32_t",
        "uint64" => "uint64_t",
        _ => return None,
    })
}

/// The column in the header that ends a text, `(LINE,COLUMN): Error: `.
fn column_of(before: &str) -> Option<usize> {
    let header = before.rsplit_once('(')?.1;
    header.split_once(',')?.1.split_once(')')?.0.parse().ok()
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
        "destructor 'value' can only be applied to datatype values constructed by 'Some'" => "the optional may be empty or the pointer may be null here.".to_string(),
        "destructor 'alt0' can only be applied to datatype values constructed by 'Alt0'"
        | "destructor 'alt1' can only be applied to datatype values constructed by 'Alt1'" => "the variant may not hold this alternative.".to_string(),
        "assertion might not hold" => "the assert line may not hold.".to_string(),
        // A contract that divides a real by a divisor that may be zero, decision 0154.
        "possible division by zero" => "the divisor may be zero.".to_string(),
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
        // A vector longer than the bound of `Vec`, decision 0164. `Vec` is the only subset type of the model.
        m if m.starts_with("value does not satisfy the subset constraints of '") => "the vector may be too long.".to_string(),
        m if m.starts_with("result of operation might violate newtype constraint for '") => {
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
    // The core reads the text of Dafny, decision 0127. The spans are into the bytes of the output.
    let reading = read_dafny(&output.as_bytes().to_vec());
    let found: Vec<Error> = reading
        .errors
        .iter()
        .enumerate()
        .map(|(k, &(line, start, end))| Error { line, column: column_of(&output[..start]), message: output[start..end].to_string(), related: reading.related.iter().filter(|(of, _)| *of == k).map(|&(_, line)| line).collect() })
        .collect();
    // A warning on a line of the companion file refuses the file, decisions 0079, 0099 and 0101. A declaration, a forall statement or a loop with no body is
    // an axiom. A lemma with no body is named at its own name, because Dafny warns at its first ensures line. Any other is named at its own line.
    let map = &t.map;
    let mut axioms: Vec<(String, usize, String)> = Vec::new();
    for (&(line, start, end), _) in reading.warnings.iter().zip(&reading.trigger).filter(|(&(line, ..), &trigger)| !trigger && line.checked_sub(1).is_some_and(|n| map.companion.contains(&n))) {
        let message = &output[start..end];
        let bodyless = message.contains("bodyless") || message.contains("{:axiom}");
        let lemma = map.decls.iter().rev().find(|(at, _)| *at <= line).filter(|(_, lemma)| *lemma && bodyless);
        let at = lemma.map_or(line, |(at, _)| *at);
        let said = if bodyless {
            format!("a {} with no body is an axiom.", if lemma.is_some() { "lemma" } else { "function" })
        } else if message.starts_with("this forall statement has no body") {
            "a forall statement with no body is an axiom.".to_string()
        } else if message.starts_with("this loop has no body") {
            "a loop with no body is an axiom.".to_string()
        } else {
            format!("Dafny warns here: {}.", message.trim().trim_end_matches('.'))
        };
        if let Some((path, number)) = map.lines[at - 1].as_ref().map(|l| map.places[l.place as usize].clone()) {
            let found = (path, number as usize, said);
            if !axioms.contains(&found) {
                axioms.push(found);
            }
        }
    }
    let unread = reading.unread;
    // A line at the end of the file, one past the last line of the companion file, is the last line, decision 0083.
    let in_companion = |line: usize| {
        let last = map.companion.end;
        in_companion_exec(line, map.companion.start, map.companion.end).then_some(line.min(last))
    };
    // The core decides: it reads the exit status, the summary, the error lines, the refusals, the axioms and the methods together, decisions 0077 and 0080.
    let verdict = judge(&reading, run.status.success(), refused, t.methods, map.companion.start, map.companion.end);
    if verdict == Verdict::ToolFailed {
        eprint!("dafny failed\n{output}");
        return Ok(ExitCode::from(2));
    }
    for (path, line, said) in &axioms {
        println!("Not provable: {}:{line}: {said}", shown(path));
    }
    let here = |line: usize| line.checked_sub(1).and_then(|n| map.lines.get(n)).and_then(Option::as_ref);
    // Dafny can report one check twice, and one check as several errors with Dafny's own related locations, such as the clauses of a strict weak order.
    // A failure prints one block for each position, sentence and set of contract lines that it shows, decisions 0155 and 0164. Two checks at one position
    // with different contract lines both stay, and so do two positions on one C++ line.
    let mut seen: Vec<(usize, Option<usize>, String)> = Vec::new();
    // A line of a function template fails in each instance that it fails in, decision 0180. A block prints as many times as one instance gives it, so the
    // count of a block is the greatest count of one instance. An instance is a method with `'of'` in its name.
    // ponytail: the text of the model is searched upward for the method. Upgrade: the core names the method of each line.
    let mut counts: HashMap<(String, usize), usize> = HashMap::new();
    let mut printed: HashMap<String, usize> = HashMap::new();
    let mut emit = |e: &Error, block: String| {
        let key = (e.line, e.column, block);
        if seen.contains(&key) {
            return;
        }
        let lines: Vec<&str> = t.dafny.lines().take(e.line).collect();
        if let Some(m) = lines.iter().rposition(|l| l.starts_with("method ")).filter(|&m| lines[m].contains("'of'")) {
            let n = counts.entry((key.2.clone(), m)).or_insert(0);
            *n += 1;
            let done = printed.entry(key.2.clone()).or_insert(0);
            if *n > *done {
                *done = *n;
                println!("{}", key.2);
            }
        } else {
            println!("{}", key.2);
        }
        seen.push(key);
    };
    // A related location in the companion file is a line of it that the failure breaks. It is shown as a contract line, as the lines of a method are, decision 0164.
    // ponytail: a clause that goes on to the next line shows its first line only, the line that Dafny names. Upgrade: read on while the next line starts
    // with `&&`, `||` or `==>`.
    let companion_clause = |r: usize| -> Option<String> {
        let at = in_companion(r)?;
        let (path, line) = map.places[here(at)?.place as usize].clone();
        Some(format!("\n  The contract line: {}:{line}: {}", shown(&path), t.dafny.lines().nth(at.checked_sub(1)?)?.trim()))
    };
    for e in &found {
        let message = e.message.trim();
        // Dafny could not read the file, so no proof ran. Each error is named at its place in the words of Dafny, decision 0080.
        if unread.is_some() {
            let at = in_companion(e.line).unwrap_or(e.line);
            let (path, line) = here(at).map_or_else(|| ("model.dfy".to_string(), at as u32), |l| map.places[l.place as usize].clone());
            emit(e, format!("Not provable: {}:{line}: Dafny says: {}.", shown(&path), message.trim_end_matches('.')));
            continue;
        }
        // A function of the model that copies lines of its method, the function of a pure member, the function of a virtual function or the upcast, fails as the
        // lines of the original do. The original reports that failure, so a failure with the same message in the original stands for this one, decision 0167.
        if let Some((_, originals)) = map.copies.iter().find(|(r, _)| r.contains(&e.line)) {
            // A call in code is a function in the function and a method in the method, so Dafny words one failure two ways, decision 0172.
            let same = |m: &str| if m == "function precondition could not be proved" { "a precondition for this call could not be proved" } else { m }.to_string();
            if found.iter().any(|o| same(&o.message) == same(&e.message) && originals.iter().any(|r| r.contains(&o.line))) {
                continue;
            }
        }
        // A failure in the lemma that checks an override names the override and the contract line of the interface that it breaks, decision 0165. Dafny
        // reports the requires half at the end of the lemma, with the requires clause that it claims as the related location, and the ensures half the same
        // way, with the ensures clause of the interface.
        if let Some(lemma) = map.lemmas.iter().find(|l| l.lines.contains(&e.line)) {
            // A requires clause of the lemma copies a requires line of the interface, which is already reported at the method of the interface. A lemma with such
            // a failure has requires lines that Dafny cannot read, so no other failure of it is true.
            if found.iter().any(|f| lemma.requires_lines.contains(&f.line)) {
                continue;
            }
            // A lemma call in the body of the check is read under the requires lines of the interface. When it fails there and not in the method of the override, the
            // override requires more than the interface, decision 0167. When it fails in the method too, the method reports it.
            if lemma.body.contains(&e.line) {
                if found.iter().any(|o| o.message == e.message && lemma.method.contains(&o.line)) {
                    continue;
                }
                let (path, line) = &map.places[lemma.place as usize];
                let mut block = format!("Not proved: {}:{line}: the override may require more than {}.", shown(path), lemma.of);
                for p in lemma.own_places.iter().chain(&lemma.requires) {
                    if let Some(text) = contract(map, *p, shown) {
                        block.push_str(&format!("\n  The contract line: {text}"));
                    }
                }
                emit(e, block);
                continue;
            }
            let (path, line) = &map.places[lemma.place as usize];
            let more = e.related.iter().any(|r| lemma.own.contains(r));
            let mut block = if more {
                format!("Not proved: {}:{line}: the override may require more than {}.", shown(path), lemma.of)
            } else {
                format!("Not proved: {}:{line}: the override may not keep the promise of {}.", shown(path), lemma.of)
            };
            let places: Vec<u32> = if more { lemma.requires.clone() } else { e.related.iter().filter_map(|r| here(*r)).map(|l| l.place).collect() };
            for p in places {
                if let Some(text) = contract(map, p, shown) {
                    block.push_str(&format!("\n  The contract line: {text}"));
                }
            }
            emit(e, block);
            continue;
        }
        // An error on a line of the companion file has no return, call or loop of a method, decisions 0084 and 0164.
        if let Some(at) = in_companion(e.line) {
            let (path, line) = here(at).map_or_else(|| ("model.dfy".to_string(), at as u32), |l| map.places[l.place as usize].clone());
            // A lemma has the sentence of the same failure in the model. A function or a predicate keeps the words of Dafny, decision 0084.
            let in_lemma = map.decls.iter().rev().find(|(start, _)| *start <= e.line).is_some_and(|(_, lemma)| *lemma);
            let said = if in_lemma { sentence(message) } else { format!("Dafny says: {}.", message.trim_end_matches('.')) };
            let clauses: String = e.related.iter().filter_map(|r| companion_clause(*r)).collect();
            emit(e, format!("Not proved: {}:{line}: {said}{clauses}", shown(&path)));
            continue;
        }
        let Some(Line { place, scope, own }) = here(e.line) else {
            // ponytail: an error on a line with no C++ place, such as a resolution error, is named by its Dafny line. Upgrade: map it to the function.
            emit(e, format!("Not proved: model.dfy:{}: {}", e.line, sentence(message)));
            continue;
        };
        let (path, line) = &map.places[*place as usize];
        // A call of trunc_div or trunc_rem whose `requires b != 0` of the prelude fails is a divisor that may be zero, decision 0088.
        let zero = message == "function precondition could not be proved"
            && e.related.iter().any(|r| PRELUDE.lines().nth(r.wrapping_sub(1)) == Some("  requires b != 0"));
        // A call of Back or PopBack whose `requires |s| > 0` of the prelude fails is a vector that may be empty, decision 0191.
        let empty = message == "function precondition could not be proved"
            && e.related.iter().any(|r| PRELUDE.lines().nth(r.wrapping_sub(1)) == Some("  requires |s| > 0"));
        // The only Dafny functions besides the prelude are the member functions, so a related requires line of the contract is one of theirs, decision 0095.
        let member = message == "function precondition could not be proved"
            && e.related.iter().filter_map(|r| here(*r)).any(|l| map.contracts.get(&l.place).is_some_and(|(word, _)| word == "requires"));
        // A call of shr whose `requires 0 <= n < w` of the prelude fails is a shift amount that may be too wide, decision 0106.
        let shift = message == "function precondition could not be proved"
            && e.related.iter().any(|r| !map.companion.contains(&r.wrapping_sub(1)) && t.dafny.lines().nth(r.wrapping_sub(1)) == Some("  requires 0 <= n < w"));
        // A call of fadd to fdiv whose bound `requires abs(...) <= MAX` of the module `Double` fails is a result that may pass DBL_MAX, and the divisor of
        // fdiv is `requires b != 0.0`, decision 0154. The lines are found by their text in the model, outside the companion file.
        let double_line = |r: &usize| t.dafny.lines().nth(r.wrapping_sub(1)).map(str::trim).filter(|_| !map.companion.contains(&r.wrapping_sub(1)));
        let overflow = message == "function precondition could not be proved"
            && e.related.iter().any(|r| double_line(r).is_some_and(|l| l.starts_with("requires abs(") && l.ends_with(") <= MAX")));
        let too_large = message == "function precondition could not be proved"
            && e.related.iter().any(|r| double_line(r) == Some("requires -9007199254740992 <= n <= 9007199254740992"));
        // StdSort is a method, so Dafny says "a precondition for this call".
        let comparator = message == "a precondition for this call could not be proved"
            && e.related.iter().any(|r| double_line(r) == Some("requires StrictWeakOrder(cmp)"));
        let double_zero = message == "function precondition could not be proved" && e.related.iter().any(|r| double_line(r) == Some("requires b != 0.0"));
        let said = if overflow {
            "the result of the operation may exceed DBL_MAX.".to_string()
        } else if comparator {
            "the comparator may not be a strict weak order.".to_string()
        } else if too_large {
            "the integer may be too large for an exact double.".to_string()
        } else if zero || double_zero {
            "the divisor may be zero.".to_string()
        } else if shift {
            "the shift amount may be negative or not below the width of the type.".to_string()
        } else if empty {
            "a requires line of the callee may not hold.".to_string()
        } else if member && map.contracts.contains_key(place) {
            "a requires line of the member function may not hold here.".to_string()
        } else if member {
            // A call of a function of the model on a line of a body is a call in code, decision 0172. It has the sentence of a method call.
            "a requires line of the callee may not hold.".to_string()
        } else {
            sentence(message)
        };
        let mut block = format!("Not proved: {}:{line}: {said}", shown(path));
        let mut told = vec![*place];
        for r in &e.related {
            if let Some(clause) = companion_clause(*r) {
                block.push_str(&clause);
                continue;
            }
            let Some(l) = here(*r) else { continue };
            if !told.contains(&l.place) {
                if let Some(text) = contract(map, l.place, shown) {
                    block.push_str(&format!("\n  The contract line: {text}"));
                    told.push(l.place);
                }
            }
        }
        if !timed_out(message) {
            // The invariants of a loop do not hold yet when the loop starts.
            let own = own.iter().filter(|_| !message.starts_with("this loop invariant could not be proved on entry"));
            for p in scope.iter().chain(own) {
                if let Some(text) = contract(map, *p, shown) {
                    block.push_str(&format!("\n  It assumes: {text}"));
                }
            }
        }
        emit(e, block);
    }
    // The count of verified items is the only fault, decision 0083.
    if let (Some((v, 0, 0)), true) = (reading.summary, found.is_empty() && !refused && axioms.is_empty() && verdict == Verdict::NotProved) {
        println!("Not provable: {source}: Dafny verified fewer items than the model has methods: {v} for {}.", t.methods);
    }
    // The proof rests on the rounding axiom when the model calls an operation of `Double`, decision 0154.
    if t.rounds {
        println!("Axiom: Double.dfy: RoundError: IEEE 754 binary64, round to nearest even, gradual underflow, one rounding per operation.");
    }
    // A call through an interface runs an override that the file checks against the contract of the interface, decision 0165.
    for interface in &t.interfaces {
        println!("Axiom: model: {interface}: a call through {interface} runs an override that keeps the contract of {interface}, C++23 [class.virtual]. Each override of {interface} in this file is checked against that contract.");
    }
    if t.sorted {
        println!("Axiom: Algorithm.dfy: StdSort: std::sort with a strict weak order gives a permutation of its range, and no later element compares less than an earlier one, C++23 [sort] and [alg.sorting.general].");
    }
    if t.exact {
        println!("Axiom: Double.dfy: RoundExactInt: an integer up to 2^53 in magnitude is a double.");
    }
    if verdict == Verdict::Proved {
        println!("ok: proved");
        return Ok(ExitCode::SUCCESS);
    }
    Ok(ExitCode::from(1))
}

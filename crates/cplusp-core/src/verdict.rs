//! The verdict of `cplusp prove`, decisions 0077, 0079 and 0080. The shell runs Dafny and reads six facts from the run. This
//! module decides from them, and it proves that `Proved` needs each of them to be clean.

use vstd::prelude::*;

verus! {

/// What a run of `cplusp prove` says. `Proved` is `ok: proved`. `NotProved` names the failed obligations or the refusals.
/// `ToolFailed` is a run of Dafny whose facts do not agree, so it gives no result, decision 0069.
#[derive(Structural, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Verdict {
    Proved,
    NotProved,
    ToolFailed,
}

/// The rule. `exit_ok` is the exit status of Dafny. `summary` is the verified items, the errors and the time-outs of its summary
/// line, or `None` when the output has no summary that can be read. `errors` is the number of error lines. `refused` says that the
/// translator refused a construct. `axioms` is the number of axioms that Dafny warns of in the companion file, decision 0079.
/// `methods` is the number of methods that the model holds, and Dafny must verify at least that many items, decision 0080. The
/// exit status, the counts and the error lines must agree, decision 0070.
pub open spec fn spec_verdict(
    exit_ok: bool,
    summary: Option<(u64, u64, u64)>,
    errors: usize,
    refused: bool,
    axioms: usize,
    methods: usize,
) -> Verdict {
    match summary {
        None => Verdict::ToolFailed,
        Some((v, e, t)) => {
            let clean = e == 0 && t == 0;
            if exit_ok != clean || (clean && errors > 0) || (!clean && errors == 0) {
                Verdict::ToolFailed
            } else if clean && !refused && axioms == 0 && v >= methods as u64 {
                Verdict::Proved
            } else {
                Verdict::NotProved
            }
        },
    }
}

/// The verdict of one run. It is `Proved` only when Dafny exits with success, the summary has zero errors and zero time-outs and
/// counts each method as verified, no error line is present, nothing is refused and the companion file holds no axiom.
pub fn verdict(exit_ok: bool, summary: Option<(u64, u64, u64)>, errors: usize, refused: bool, axioms: usize, methods: usize) -> (v:
    Verdict)
    ensures
        v == spec_verdict(exit_ok, summary, errors, refused, axioms, methods),
        v == Verdict::Proved <==> (exit_ok && summary.is_some() && summary.unwrap().1 == 0 && summary.unwrap().2 == 0 && summary.unwrap().0
            >= methods as u64 && errors == 0 && !refused && axioms == 0),
        summary.is_none() ==> v == Verdict::ToolFailed,
{
    match summary {
        None => Verdict::ToolFailed,
        Some((v, e, t)) => {
            let clean = e == 0 && t == 0;
            if exit_ok != clean || (clean && errors > 0) || (!clean && errors == 0) {
                Verdict::ToolFailed
            } else if clean && !refused && axioms == 0 && v >= methods as u64 {
                Verdict::Proved
            } else {
                Verdict::NotProved
            }
        },
    }
}

} // verus!

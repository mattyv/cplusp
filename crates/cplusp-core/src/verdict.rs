//! The verdict of `cplusp prove`, decision 0077. The shell runs Dafny and reads four facts from the run. This module decides from
//! them, and it proves that `Proved` needs all four to be clean.

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

/// The rule. `exit_ok` is the exit status of Dafny. `summary` is the errors and the time-outs of its summary line, or `None` when
/// the output has no summary that can be read. `errors` is the number of error lines. `refused` says that the translator refused
/// a construct. The exit status, the counts and the error lines must agree, decision 0070.
pub open spec fn spec_verdict(exit_ok: bool, summary: Option<(u64, u64)>, errors: usize, refused: bool) -> Verdict {
    match summary {
        None => Verdict::ToolFailed,
        Some((e, t)) => {
            let clean = e == 0 && t == 0;
            if exit_ok != clean || (clean && errors > 0) || (!clean && errors == 0) {
                Verdict::ToolFailed
            } else if clean && !refused {
                Verdict::Proved
            } else {
                Verdict::NotProved
            }
        },
    }
}

/// The verdict of one run. It is `Proved` only when Dafny exits with success, the summary has zero errors and zero time-outs, no
/// error line is present and nothing is refused.
pub fn verdict(exit_ok: bool, summary: Option<(u64, u64)>, errors: usize, refused: bool) -> (v: Verdict)
    ensures
        v == spec_verdict(exit_ok, summary, errors, refused),
        v == Verdict::Proved <==> (exit_ok && summary == Some((0u64, 0u64)) && errors == 0 && !refused),
        summary.is_none() ==> v == Verdict::ToolFailed,
{
    match summary {
        None => Verdict::ToolFailed,
        Some((e, t)) => {
            let clean = e == 0 && t == 0;
            if exit_ok != clean || (clean && errors > 0) || (!clean && errors == 0) {
                Verdict::ToolFailed
            } else if clean && !refused {
                Verdict::Proved
            } else {
                Verdict::NotProved
            }
        },
    }
}

} // verus!

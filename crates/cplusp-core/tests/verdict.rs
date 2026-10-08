//! The verdict of `cplusp prove` on every combination of the facts it reads, decisions 0077, 0079 and 0080.

use cplusp_core::verdict::*;

#[test]
fn proved_needs_each_fact_clean_and_every_method_verified() {
    for exit_ok in [true, false] {
        // The summary: verified, errors and time-outs.
        for summary in [None, Some((2, 0, 0)), Some((5, 0, 0)), Some((1, 0, 0)), Some((0, 0, 0)), Some((2, 1, 0)), Some((2, 0, 1)), Some((0, 2, 3))] {
            for errors in [0usize, 1, 2] {
                for refused in [true, false] {
                    for axioms in [0usize, 1] {
                        for methods in [0usize, 2] {
                            let clean = matches!(summary, Some((_, 0, 0)));
                            let agree = summary.is_some() && exit_ok == clean && (errors == 0) == clean;
                            let seen = matches!(summary, Some((v, _, _)) if v >= methods as u64);
                            let want = if !agree {
                                Verdict::ToolFailed
                            } else if clean && !refused && axioms == 0 && seen {
                                Verdict::Proved
                            } else {
                                Verdict::NotProved
                            };
                            let got = verdict(exit_ok, summary, errors, refused, axioms, methods);
                            assert_eq!(got, want, "{exit_ok} {summary:?} {errors} {refused} {axioms} {methods}");
                        }
                    }
                }
            }
        }
    }
}

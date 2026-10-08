//! The verdict of `cplusp prove` on every combination of the facts it reads, decisions 0077 and 0079.

use cplusp_core::verdict::*;

#[test]
fn proved_needs_a_clean_exit_a_clean_summary_no_error_line_no_refusal_and_no_axiom() {
    for exit_ok in [true, false] {
        for summary in [None, Some((0, 0)), Some((1, 0)), Some((0, 1)), Some((2, 3))] {
            for errors in [0usize, 1, 2] {
                for refused in [true, false] {
                  for axioms in [0usize, 1, 3] {
                    let clean = summary == Some((0, 0));
                    let agree = summary.is_some() && exit_ok == clean && (errors == 0) == clean;
                    let want = if !agree {
                        Verdict::ToolFailed
                    } else if clean && !refused && axioms == 0 {
                        Verdict::Proved
                    } else {
                        Verdict::NotProved
                    };
                    assert_eq!(verdict(exit_ok, summary, errors, refused, axioms), want, "{exit_ok} {summary:?} {errors} {refused} {axioms}");
                  }
                }
            }
        }
    }
}

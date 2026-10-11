# 0127: The core reads the output of Dafny

Date: 2026-10-11. Status: decided. Amends 0068, 0069, 0077, 0079, 0080 and 0083.

## Decision

The reader of the output of Dafny moves from the shell into the Verus core. The verdict of 0077 is in the core already. Now the facts that it reads come from the core too. The output of `prove` does not change.

- The shell gives the core the output of Dafny as bytes. The core gives the summary and the error lines with their related lines. It also gives the warning lines, and the kind of a summary for a file that Dafny cannot read. Each line number and message is as Dafny prints it. The shell makes the sentences from them, as before.
- The core then judges. It takes the exit status, the refusals, the number of methods and the lines of the companion file. A parse error counts as the author's only when each error is on a line of the companion file, decision 0083. A warning on a line of the companion file is an axiom, except a missing trigger, decision 0079.
- The core proves that `proved` needs all of these facts in the text. The output has a summary line with zero errors and zero time-outs, and no earlier line has the shape of a summary. No line is an error line. No line is a warning on the companion file other than a missing trigger. Dafny exits with success, the translator refuses nothing, and the summary counts at least as many verified items as the model has methods.
- The reader trims only ASCII white space at the end of a summary line. The shell also trimmed the other white space of Unicode. Dafny prints none.
- The shell counted an axiom only when its line had a place in the C++. The core counts each such warning on the companion file. So a warning with no place now stops `proved` too.

## Why

The reader decides what Dafny said. If it misreads the summary or misses an error line, `prove` can say `ok: proved` for a proof that failed. Decision 0077 puts each such decision in the core. The user chose this move third.

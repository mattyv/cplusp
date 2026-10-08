# 0069: `prove` trusts only a finished run of Dafny, runs the team's gate, and gives each obligation its own line and assumptions

Date: 2026-10-08. Status: decided. Amends 0068 after its review.

## Decision

- `prove` reads a run of Dafny as a result only when Dafny prints its summary, `Dafny program verifier finished with`. Some runs have no summary: a model that does not parse, empty output, or a crash. Such a run is no proof and no failure of the C++. `prove` prints `dafny failed` and the output on stderr, and exits 2.
- The translator refuses a name with a character that Dafny cannot read, so each model parses. Clang accepts `$` and other characters in a name. The refusal names the function's line and the name.
- `prove` takes `--policy`, as `cplusp gate` does, and runs the gate under that policy. A row that a team tightened refuses the file before any proof.
- A failed ensures says that the line may not hold. Dafny says only that it could not prove the line. A true line with a weak invariant gets the same message.
- The start and the step of a `for` keep their own lines. The core gives each its place.
- An obligation on an `ensures` line assumes the `requires` lines. An obligation that the loop keeps an invariant assumes all the invariants of that loop. An obligation that an invariant holds when the loop starts assumes only what holds before the loop.
- `docs/plan.md` lists `prove` and its reader of the output of Dafny as a trusted edge.

## Why

The review of 0068 found that a model Dafny could not parse came out as one `Not proved` line. Every other function went unverified with no word. A stand-in for Dafny that printed nothing gave `ok: proved`. `prove` ran the default policy, so a team's tighter gate could be passed by `prove`. The other findings put an obligation at the wrong line or with the wrong assumptions, and those are what the bot reads.

## What changes

The core gives the start and the step of a `for` their places. The shell reads the summary of Dafny, refuses names Dafny cannot read, takes `--policy`, and fixes the scope of contract lines.

# 0068: `cplusp prove` runs the gate, the translator and the prover, and names each failed obligation in C++

Date: 2026-10-08. Status: decided. Follows 0065 and 0066, and keeps the reliance of 0067.

## Decision

- `cplusp prove FILE -- FLAGS` runs the gate first. When the gate refuses the file, `prove` prints the gate's findings and stops. So the reliance of 0067 is part of the command.
- Then it translates the file and prints each refusal, as `cplusp model` does. Then it runs Dafny on the model with a time limit, 20 seconds for each method unless `--time-limit` says otherwise.
- For each obligation that Dafny does not prove, `prove` prints one line that starts with `Not proved:`. The line names the C++ file and line of the statement or the contract line. Then one sentence says what failed. Under it, it prints the contract line that the obligation comes from, when there is one. It also prints the assumptions in scope: the `requires` lines of the function, and the invariants of the loops that hold the statement. Each of these lines names its own file and line and holds the text of the contract line.
- A failure and a time limit are different results. A failure says what does not hold. A method that reaches the time limit says that the prover stopped and the result is unknown.
- A known message of Dafny gets a sentence in Simplified Technical English. Any other message keeps the words of Dafny after `Dafny says:`.
- `prove` exits 0 only when the gate passes, nothing is refused and Dafny proves each method. It exits 1 when something is not proved or refused, and 2 when the file does not compile or the prover cannot run.
- The core gives each Dafny statement and each contract line the place of the C++ statement or line that it comes from. So the line that `prove` names is the rule of the core, not a guess of the shell.

## Why

The report of 0065 cites a study of an agent that proves code. When it got only accept or reject in place of detailed feedback from the prover, its success fell from 93% to 58%. That number is from another system. It is still a strong reason to give the bot four things. They are the failed obligation, its place, the assumptions it had, and whether the prover failed or ran out of time. Before this decision, a bot had to run Dafny by hand and read lines of a file it did not write.

## What changes

The core carries a place on each statement and each contract line of a method. The shell gains `prove`, a map from each line of the Dafny text to its C++ place, and a reader of the output of Dafny.

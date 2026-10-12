# 0130: The Dafny names stay in the shell, two flag gaps close, and system headers stay documented

Date: 2026-10-12. Status: decided. Amends 0077, 0128 and 0129.

## Decision

- The Dafny names stay in the shell, and the fourth move of the R2 plan does not happen. Each defect in the names gives a refusal or an error from Dafny, so it never gives `ok: proved`. The shell adds one guard. If it drops a function and has no refusal, it adds a refusal.
- The gate refuses `-ansi` and `--ansi` with the reason `Std`. Each one sets C++98, and a later one wins over a `-std=c++23` before it.
- The gate refuses a flag that takes the next flag as its value, when the next flag starts with `-`. A lone `-` is a value, not a flag. The reason is `Swallows`. The flags are `-I`, `-isystem`, `-idirafter`, `-iquote`, `-include`, `-imacros`, `-D`, `-U`, `-x`, `-o`, `-MF`, `-MT`, `-MQ`, `-Xclang`, `-Xpreprocessor`, `-target`, `-isysroot`, `-cxx-isystem` and `-isystem-after`. So `-I -std=c++23` cannot hide the `-std` from the compiler while the gate counts it.
- The core proves both refusals with the other facts of a run with no refusal, decision 0128.
- A header behind `-isystem` stays a documented limit of the gate, in docs/soundness.md. The gate does not refuse `-isystem` for a path in the project.

## Why

The user asked the reviewer for advice on these three questions, and the user chose its advice. The reviewer found no way for a defect in the names to give `ok: proved`. Every dropped function comes with a refusal, and two functions share a name only when they share a key, which Dafny refuses. A move to the core costs about 300 lines for no new safety. The reviewer also tested a read of the final flags from the compiler with `-###`. That output has the same shape as the input, so it needs the same list of flags, and a fix in the core is simpler. For `-isystem`, `prove` already refuses each call into such a header, because nothing there has a model. A refusal of `-isystem` would refuse real builds, where the code of others is often under the project folder.

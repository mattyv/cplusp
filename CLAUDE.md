# Working on cplusp

`docs/plan.md` is the design. `docs/policy.md` is the policy file format. `docs/decisions/` is the decision log: one numbered file per decision, never edited after the fact, a new file to reverse one. Amend them rather than contradict them. A decision made in conversation is not made until it has a file.

## One proof after another

Every module lands with its proof or with a named reason why it has none.

- `crates/cplusp-core` is written in Verus. `cargo verus verify` must pass with zero errors before a commit. Specs are the deliverable, not decoration: a function with a trivial `ensures` is unfinished.
- Code that Verus cannot reach (file I/O, process launch, YAML parsing, text rendering) lives in `crates/cplusp` and nowhere else. It is the trusted edge. Keep it thin and keep it listed in `docs/plan.md`.
- Never move logic from the core to the shell to dodge a proof. Restructure the data until the proof goes through.

## Test-driven, always

Write the failing test first. Watch it fail and read the message. If the message does not name the real defect, the test is wrong. Only then make it pass.

- Assert the observable outcome, not the shape of the output. For the gate that means the message a bot would read, word for word.
- Prefer one invariant test over a pile of spot checks.
- Goldens are reviewed, never blind-accepted. When one changes, say why in the commit.
- Every rule in the policy has a sample pair under `rules/<id>/`: `allowed.cpp` passes the gate, `banned.cpp` fails on the marked lines. The pair is the proof that the check means what the row says.

## Lazy, in the senior-developer sense

The ponytail ladder applies to every change. Stop at the first rung that holds:

1. Does this need to exist at all? Speculative need: skip it and say so in one line.
2. Already in this codebase? Reuse it. The core crate before the shell, the shell before a new module.
3. Standard library does it? Use it.
4. An installed dependency does it? Use it. Never add one for what a few lines can do.
5. Can it be one line? One line.
6. Only then: the minimum code that works.

Fewest files. No interface with one implementation, no config for a value that never changes, no scaffolding for later. Mark a deliberate corner cut with a `ponytail:` comment that names the ceiling and the upgrade path. Never lazy about understanding the problem first, and never lazy about the two things this repo exists for: the failing test comes first, and the proof is part of the deliverable.

## Messages

Everything the bot reads follows Simplified Technical English: short sentences, one meaning per word, no semicolons. The prefixes are fixed: `Not provable:` from the gate, `Not proved:` from the prover. Lint the docs with `ste-lint.py` from the asd-ste100 skill before committing them.

## Toolchain

Rust is pinned in `rust-toolchain.toml` to the version the Verus release needs. Verus itself is the release named in `docs/plan.md`. clang-tidy is 18 from Ubuntu 24.04 apt.

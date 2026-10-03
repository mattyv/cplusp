# Working on cplusp

`docs/plan.md` is the design. `docs/policy.md` is the policy file format. Amend them rather than contradict them.

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

## Messages

Everything the bot reads follows Simplified Technical English: short sentences, one meaning per word, no semicolons. The prefixes are fixed: `Not provable:` from the gate, `Not proved:` from the prover. Lint the docs with `ste-lint.py` from the asd-ste100 skill before committing them.

## Toolchain

Rust is pinned in `rust-toolchain.toml` to the version the Verus release needs. Verus itself is the release named in `docs/plan.md`. clang-tidy is 18 from Ubuntu 24.04 apt.

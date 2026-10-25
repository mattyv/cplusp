# Working on cplusp

Start with `README.md` for current behaviour, proof limits and check commands. `docs/plan.md` is the historical design. `docs/policy.md` is the policy file format. `docs/decisions/` is the decision log: one numbered file per decision, never edited after the fact, a new file to reverse one. Amend them rather than contradict them. A decision made in conversation is not made until it has a file.

## One proof after another

Every module lands with its proof or with a named reason why it has none.

- `crates/cplusp-core` is written in Verus. `cargo verus verify` must pass with zero errors before a commit. Specs are the deliverable, not decoration: a function with a trivial `ensures` is unfinished.
- Code that Verus cannot reach lives in two places and nowhere else. File I/O, process launch, YAML parsing and text rendering live in `crates/cplusp`. The clang-tidy plugin lives in `clang-tidy/` and is C++ because clang-tidy allows nothing else. Both are trusted edges. Keep them thin and keep them listed in `docs/plan.md`. The plugin's evidence is the sample pairs.
- Never move logic from the core to the shell to dodge a proof. Restructure the data until the proof goes through.

## How a change happens

Three roles, in order, for every change. The agent files are in `.claude/agents/`.

1. **Fable writes the failing tests**, and the fixtures and sample pairs they need. Red step. Committed as such.
2. **The `coder` agent (Sonnet) makes them green** against the reviewed requirements, contracts and tests. It never changes one. If they conflict, or a test cannot be met, it reports the conflict instead.
3. **The `reviewer` agent (Fable) reviews the diff.** It tries to break each contract with deliberately wrong implementations, and it checks that intended inputs meet the preconditions. Findings go back to the coder, with new failing tests for any behaviour change. Then Fable runs the suite and the proofs, commits the green step, and pushes.

The reviewer decides each change to a requirement, a contract or a test, and Fable writes it, decision 0066. Fable also writes the Verus core and its proofs, and the docs. Sonnet does not touch the core.

Build in small increments, and prove each one before you build on it. When a proof gets hard, change the data structures or the helper boundaries. Never weaken a reviewed contract to make a proof pass.

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

Fewest files. No interface with one implementation, no config for a value that never changes, no scaffolding for later. Mark a deliberate corner cut with a `ponytail:` comment that names the ceiling and the upgrade path. Never lazy about understanding the problem first. Never lazy about the two things this repo exists for: the failing test comes first, and the proof is part of the deliverable.

## Talking to the user

The user vibe codes. The user does not read the code. Follow `.claude/skills/vibe-coding/SKILL.md` in each message to the user: say what changed in behaviour and what is next, in plain words. Make the technical choices yourself, and ask only questions that change scope, cost or direction. The coder and the reviewer report to you in full detail, as before.

## Messages

Everything the bot reads follows Simplified Technical English: short sentences, one meaning per word, no semicolons. The prefixes are fixed: `Not provable:` from the gate, `Not proved:` from the prover. Lint the docs with `ste-lint.py` from the asd-ste100 skill before committing them.

## Toolchain

Rust is pinned in `rust-toolchain.toml` to the version the Verus release needs. Verus is built from revision `11ed7501a8ba5160be537da21cca330dafbecb9b`, matching `vstd`. The Checks workflow records the build commands. clang-tidy is 18 from Ubuntu 24.04 apt, with `clang-18` for the preprocessor the gate runs. `libclang-18-dev` and `llvm-18-dev` give the plugin headers and CMake files. Build the plugin with `cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin`. The tests look for it at `target/plugin/libcplusp.so` or `$CPLUSP_PLUGIN`.

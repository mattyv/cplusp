# Divergence battery

A proof is about a model. These cases find where a naive Dafny model of a piece of C+P code means something different from the C++, and record the mitigation. Decision 0017.

Each case is a folder under `cases/` with:

- `code.cpp`: the C++ as the bot might write it, with its `//@` contract. It passes the gate.
- `naive.dfy`: the obvious transliteration. Written to show the divergence.
- `mitigated.dfy`: the transliteration under the rule. Or the same C++ changed, when the mitigation is on the C++ side.
- `witness.cpp`: a `main` that drives `code.cpp` to the edge where the two part ways.
- `case.yaml`: the expectations and the report fields. `gap` is the section of docs/soundness.md the case belongs to. `cpp` says what the C++ does, `naive_does` what the naive model does instead. `side` says where the mitigation lives: `model`, `cpp`, `gate` or `none` when the model is only stricter. `mitigation` is one line for the report. What Dafny must say about each file, `verifies` or `fails`. Whether the naive verdict is wrong. What the witness shows, `ubsan: true` for undefined behaviour or `prints` for an output. And the rule in words.

`cargo run -p divergence` generates `docs/mitigations.md` from the cases. Do not edit it by hand. The rule of every case appears in `skills/cplusp-dafny/SKILL.md`, which is what the LLM reads when it writes Dafny for C+P. The test in `crates/divergence` runs every case and checks that the skill file carries its rule, so the two cannot drift.

Tools: Dafny at `$DAFNY`, else `/opt/dafny/dafny/dafny`, else `dafny` on PATH. clang++ 18 with the sanitizer runtime (`libclang-rt-18-dev`).

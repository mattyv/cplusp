# Divergence battery

A proof is about a model. These cases find where a naive model of a piece of C+P code means something different from the C++, and record the mitigation. Decision 0017. There is one battery per prover, decision 0018. `dafny/` holds the Dafny cases, `docs/mitigations-dafny.md` is its report, and `skills/cplusp-dafny/SKILL.md` is its skill.

`dafny/Double.dfy` is the shared model of `double`: a real after one rounding per operation, with the IEEE 754 error bound as an axiom. A double case includes it. Its header lists what it assumes about the build.

Each case is a folder under `<prover>/cases/` with:

- `code.cpp`: the C++ as the bot might write it, with its `//@` contract. It passes the gate. When the mitigation is a gate row, the gate reports it under that row instead.
- `naive.dfy`: the obvious transliteration. Written to show the divergence.
- `mitigated.dfy`: the transliteration under the rule.
- `fixed.cpp`: the C++ changed under the rule. Only when the side is `cpp` or `gate`. It passes the gate, and it prints the same under clang and g++.
- `witness.cpp`: a `main` that drives `code.cpp`, or `fixed.cpp`, to the edge where the two part ways.
- `case.yaml`: the expectations and the report fields.

The fields of `case.yaml`:

- `construct`: what the case is about, for the report.
- `standard`: the section of the C++ standard that decides the case, as `[label]: the sentence`. The labels are those of eel.is. A sentence may be shortened.
- `row`: the id of the policy row the case exercises. Every row the policy allows or restricts has at least one case, which is how the battery covers the subset.
- `gap`: the section of docs/soundness.md the case belongs to.
- `cpp`: what the C++ does. `naive_does`: what the naive model does instead.
- `naive`, `mitigated`: what Dafny must say about each file. `verifies`, `fails`, or `type_error` when Dafny refuses the file before it verifies anything. The mitigated model always verifies.
- `naive_is_wrong`: the naive model verifies, and the C++ can do otherwise. The report shows `verifies, wrong`.
- `side`: where the mitigation lives. `model`: the Dafny differs from the literal model. `contract`: the `//@` contract gains a clause, in the C++ and in the model, and the caller carries it. `cpp`: the C++ body changes. `gate`: a policy row refuses the C++. `gate_rule` names the row, and the sample pair under `rules/` shows it. `none`: no mitigation, because the literal model is exact.
- `mitigation`: one line for the report. For a `model` or `contract` side, the rule lines carry the C++ contract under the rule. `code.cpp` stays the C++ as the bot wrote it.
- `witness`: `input` in words. `ubsan: true` when the witness hits undefined behaviour. `asan: true` when it hits AddressSanitizer or LeakSanitizer, for a lifetime bug or a leak. `tsan: true` when it hits ThreadSanitizer, for a data race. `prints` for its output under clang. `prints_gcc` when g++ prints something else, which shows an unspecified result. `fixed_prints` for the output of `fixed.cpp`, the same under both compilers.
- `rule`: the rule in words. Every line appears in the skill file.

`cargo run -p divergence -- dafny` generates `docs/mitigations-dafny.md` from the cases. Do not edit it by hand. The test in `crates/divergence` runs every case through Dafny, the gate, the witness under the sanitizer, and the skill file. So the cases, the report and the skill cannot drift.

Tools: Dafny at `$DAFNY`, else `/opt/dafny/dafny/dafny`, else `dafny` on PATH. clang++ 18 with the sanitizer runtime (`libclang-rt-18-dev`), g++, and the gate's plugin at `target/plugin/libcplusp.so` or `$CPLUSP_PLUGIN`.

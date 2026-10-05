# Decision log

One file per decision, numbered in the order we made them. A file is short: the date, the status, the decision in one or two sentences, why, and what it changes. A reversed decision gets a new file that names the old one. Nothing is edited after the fact.

Status is `decided`, `proposed` (the default until someone objects or the thin slice settles it) or `superseded by NNNN`.

| No. | Decision | Status |
| --- | --- | --- |
| [0001](0001-llm-loop-first.md) | The tool serves the LLM coding loop first. CI is a backstop | decided |
| [0002](0002-provable-and-proved.md) | Provable is the gate's word, proved is the prover's | decided |
| [0003](0003-three-kinds-of-function.md) | Verified, trusted and plain functions. Verified code calls only contracted code | decided |
| [0004](0004-no-undefined-behaviour.md) | No undefined behaviour in verified code, split between gate and prover | decided |
| [0005](0005-gate-runs-separately.md) | The gate runs apart from a team's own clang-tidy, with its own pinned clang-tidy | decided |
| [0006](0006-policy-file.md) | One policy file holding decisions and detection. Teams may loosen with a reason | decided |
| [0007](0007-prover-is-a-plugin.md) | The prover is a plug-in. Dafny or VeriFast first, settled by the thin slice | decided |
| [0008](0008-rust-with-verus.md) | The driver is Rust written in Verus. C++ only for the clang-tidy module. No Python | decided |
| [0009](0009-no-ply.md) | Ply is not a dependency for now | decided |
| [0010](0010-how-we-work.md) | Test first, proofs in, the ponytail ladder, Sonnet implements and Fable reviews | decided |
| [0011](0011-state-in-contracts.md) | Members are implicit. Globals and statics are listed in reads or modifies | proposed |
| [0012](0012-shared-variables.md) | Variables other threads may change enter verified code only as values | proposed |
| [0013](0013-gate-flag.md) | A row is gate-enforced when its stage is gate, or it has detect and a decision other than allow | decided |
| [0014](0014-gate-refusals.md) | The gate refuses what it cannot judge: compile errors, NOLINT, bad build dirs, loose YAML | decided |
| [0015](0015-scope-gate-only.md) | Build the gate and nothing past it until told otherwise | decided |
| [0016](0016-data-driven-plugin.md) | One generic clang-tidy check driven by matcher patterns in the policy | decided |
| [0017](0017-hand-written-dafny-and-divergence-battery.md) | No translator yet. Hand-written Dafny under rules found by a divergence battery | decided |
| [0018](0018-one-battery-per-prover.md) | One divergence battery, one skill and one mitigation report per prover | decided |
| [0019](0019-floats-as-a-real-after-rounding-on-trial.md) | Floating point stays in the subset on trial, modelled as a real after rounding | decided, on trial |
| [0020](0020-floats-stay-with-three-corrections.md) | Floating point stays, with a corrected error axiom, a required flag, and a contract spelling for bounds | decided |
| [0021](0021-the-gate-requires-the-build-the-proofs-assume.md) | The gate refuses a build the proofs cannot follow: fast math, a standard below C++20, a silenced warning | decided |
| [0022](0022-the-baseline-is-cpp23.md) | Verified code is C++23 or later | decided |
| [0023](0023-the-float-error-axiom-carries-an-absolute-term.md) | The float error axiom is relative error plus half a subnormal, with no lower bound | decided |
| [0024](0024-verified-code-is-double-only.md) | Verified code uses `double` and no other floating-point type | decided |
| [0025](0025-the-gate-refuses-what-it-cannot-enforce.md) | A run that cannot enforce every row is refused, the compile database flags are judged, pragmas are findings, two rows move to the prover | decided |
| [0026](0026-state-changes-in-one-expression-follow-the-standards-order.md) | Two changes of state in one expression are allowed only where the standard orders them | decided |
| [0027](0027-floating-literals-are-exact-or-refused.md) | A floating-point literal is exactly a double, or the gate refuses it | decided |
| [0028](0028-member-functions-use-the-implicit-this.md) | A member function's contract uses the implicit `this`, members are never listed, the invariant is a predicate method | decided |

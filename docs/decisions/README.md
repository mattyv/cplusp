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
| [0011](0011-state-in-contracts.md) | Members are implicit. Globals and statics are listed in reads or modifies | decided |
| [0012](0012-shared-variables.md) | Variables other threads may change enter verified code only as values | proposed |
| [0013](0013-gate-flag.md) | A row is gate-enforced when its stage is gate, or it has detect and a decision other than allow | decided |
| [0014](0014-gate-refusals.md) | The gate refuses what it cannot judge: compile errors, NOLINT, bad build dirs, loose YAML | decided |
| [0015](0015-scope-gate-only.md) | Build the gate and nothing past it until told otherwise | superseded by 0017 |
| [0016](0016-data-driven-plugin.md) | One generic clang-tidy check driven by matcher patterns in the policy | decided |
| [0017](0017-hand-written-dafny-and-divergence-battery.md) | No translator yet. Hand-written Dafny under rules found by a divergence battery | decided |
| [0018](0018-one-battery-per-prover.md) | One divergence battery, one skill and one mitigation report per prover | decided |
| [0019](0019-floats-as-a-real-after-rounding-on-trial.md) | Floating point stays in the subset on trial, modelled as a real after rounding | decided, on trial |
| [0020](0020-floats-stay-with-three-corrections.md) | Floating point stays, with a corrected error axiom, a required flag, and a contract spelling for bounds | decided |
| [0021](0021-the-gate-requires-the-build-the-proofs-assume.md) | The gate refuses a build the proofs cannot follow: fast math, a standard below C++20, a silenced warning | decided |
| [0022](0022-the-baseline-is-cpp23.md) | Verified code is C++23 or later | decided |
| [0023](0023-the-float-error-axiom-carries-an-absolute-term.md) | The float error axiom is relative error plus half a subnormal, with no lower bound | decided |
| [0024](0024-verified-code-is-double-only.md) | Verified code uses `double` and no other floating-point type | decided |
| [0025](0025-the-gate-refuses-what-it-cannot-enforce.md) | A run that cannot enforce every row is refused, the compile database flags are judged, pragmas are findings, two rows move to the prover | decided, global_state back to the gate by 0035 |
| [0026](0026-state-changes-in-one-expression-follow-the-standards-order.md) | Two changes of state in one expression are allowed only where the standard orders them | decided |
| [0027](0027-floating-literals-are-exact-or-refused.md) | A floating-point literal is exactly a double, or the gate refuses it | decided |
| [0028](0028-member-functions-use-the-implicit-this.md) | A member function's contract uses the implicit `this`, members are never listed, the invariant is a predicate method | decided |
| [0029](0029-the-model-has-no-heap.md) | The model has no heap. An object is a value, a method takes it in and gives it back, no reference member or local | decided |
| [0030](0030-const-reaches-through-a-handle-and-a-static-local-is-refused.md) | Const reaches through a `unique_ptr`, a function-local static is refused, two matcher holes closed | decided |
| [0031](0031-text-is-bytes-in-verified-code.md) | Text is bytes in verified code. `std::string` is trusted only, a search returns an optional | decided |
| [0032](0032-the-gate-is-an-allowlist.md) | The gate is an allowlist of node kinds. A kind it does not list is refused | decided |
| [0033](0033-one-root-one-writer.md) | One root, one writer. No two names for one object in a call, no write through a const handle, no read beside an unordered change | decided |
| [0034](0034-the-differential-run-is-the-first-match-check.md) | The differential run is the first match check. The model and the C++ run on the same inputs, and the naive model must part ways | decided |
| [0035](0035-unlisted-state-is-the-gates.md) | Unlisted state is the gate's. It reads the `modifies` and `reads` lines and refuses an access they do not list | decided |
| [0036](0036-an-analysis-that-cannot-finish-refuses.md) | An analysis that cannot finish refuses. Templates are judged where used, an unread callee changes state, no budget ends in a pass, the compiler reads the source | decided |
| [0037](0037-the-gate-reads-the-compilers-lowered-form.md) | The gate reads the compiler's lowered form. The state check judges the code clang generates, where nothing is implicit, and the plugin reads the directives from the preprocessor | decided |
| [0038](0038-what-runs-counts-and-only-the-compiler-reads.md) | What runs counts, and only the compiler reads the source. Pragmas come from the preprocessor's callbacks, every operation that runs adds its effect, const reaches through a return | decided |
| [0039](0039-the-gate-reads-the-markers.md) | The gate reads the markers. A finding takes the kind of the function that holds it, the core decides what stands, and the gate refuses a broken marker | decided |
| [0040](0040-a-const-handle-gives-reads-only.md) | A const handle gives reads only. The const-handle check lists the reads and refuses every other use of what a const handle gives | decided |
| [0041](0041-what-carries-a-way-to-write-is-no-read.md) | What carries a way to write is no read. A const method's result, a copy or a const reference that holds a pointer, a span or a handle is followed, not read | decided |
| [0042](0042-a-const-unique-ptr-carries-nothing-unjudged.md) | A const unique_ptr carries nothing unjudged. It cannot be copied, and every use of what it owns is judged, so a const reference to one is a read | decided |
| [0043](0043-a-library-type-counts-by-what-it-holds.md) | A library type counts by what it holds. Fields and bases count for every record, const reaches the fields, owning containers count by their elements, an incomplete type carries | decided |
| [0044](0044-an-owning-container-counts-by-all-its-type-arguments.md) | An owning container counts by all its type arguments. A library constructor reads only a value of its own type or of a type argument | decided |
| [0045](0045-a-library-constructor-reads-only-a-library-value.md) | A library constructor reads only a number or a value of the library. A type of the file copies through its own constructor, which may write | decided |
| [0046](0046-a-library-type-is-a-library-value-only-when-what-it-holds-is.md) | A library type is a value of the library only when each type argument is a number, an enum or a value of the library | decided |
| [0047](0047-verified-code-runs-no-plain-code-and-each-function-has-its-own-kind.md) | Verified code runs no plain code, read from the lowered form. Each function has its own kind, and each build is its own run | decided |
| [0048](0048-an-indirect-call-counts-where-it-runs-and-code-in-a-plain-body-is-plain.md) | An indirect call counts where it runs, a virtual call reaches every override, code in a plain body is plain | decided |
| [0049](0049-an-indirect-call-is-named-by-constants-alone.md) | An indirect call is named by constants alone. A pointer from a parameter, a call or memory a call can write has no name | decided |
| [0050](0050-a-function-passed-by-name-is-a-pointer-the-callee-holds.md) | A function passed by name is a pointer that the callee holds. A lambda passed straight to the std call is the way | decided |
| [0051](0051-a-type-can-be-plain.md) | A type can be plain. Verified code makes no object of it and reads no field of it, and reaches it through a trusted member | decided |

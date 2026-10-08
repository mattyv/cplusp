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
| [0052](0052-a-plain-object-goes-only-to-the-files-own-code.md) | A plain object goes only to the file's own code. No value that holds a plain type, and no call of the library with one | decided |
| [0053](0053-a-pointer-counts-as-the-object-and-a-friend-of-a-plain-type-is-plain.md) | A pointer to a plain object counts as the object. A friend defined in a plain type is plain | decided |
| [0054](0054-a-cast-of-a-pointer-to-a-plain-object-is-a-use.md) | A cast of a pointer to a plain object into another pointer type is a use | decided |
| [0055](0055-writes-templates-and-proxies-by-what-the-compiler-resolves.md) | Writes, templates and proxies count by what the compiler resolves: a non-const rvalue reference writes, type checks read instantiations, a library proxy is a reference | decided |
| [0056](0056-the-translator-is-the-gate-and-its-decisions-are-proved.md) | The translator is the gate, and its decisions live in the Verus core. The plugin only writes the tree as data | decided |
| [0057](0057-the-tree-crosses-as-json-in-the-cores-shape.md) | No external translator. The plugin writes the tree as JSON in the core's shape, and the first slice is clamp | decided |
| [0058](0058-locals-integral-casts-and-calls.md) | The second slice: locals, integral casts, braced values and calls. A call stands alone, and each name is declared once | decided |
| [0059](0059-a-function-is-keyed-by-its-mangled-name.md) | A function is keyed by its mangled name. A Dafny name that the shell makes up has a `'`, which C++ cannot write | decided |
| [0060](0060-literal-types-contract-places-and-two-kinds-of-name.md) | A literal carries its type. A contract reads the parameters of its declaration by place. Methods are `c_`, variables `v_` | decided |
| [0061](0061-loops-writes-and-unsigned-types.md) | The third slice: loops with invariant and decreases, writes to locals, uint32 and uint64 with no wrap, typed literals | decided |
| [0062](0062-a-loop-contract-reads-the-variables-in-scope.md) | A loop contract reads the variables in scope. A contract line after code belongs to nothing. A loop does not take its function's lines | decided |
| [0063](0063-bool-literals-full-unsigned-literals-and-places.md) | Bool literals, literals over the full unsigned range, and a refusal of a contract line at its own file | decided |
| [0064](0064-read-only-sequences-and-forall.md) | The fourth slice: read-only span and vector parameters as Dafny sequences, size and index, forall and chained comparisons in contracts | decided |
| [0065](0065-requirements-contracts-and-composition.md) | Derive contracts from requirements. Prove components and composition. Validate translation and report assumptions | decided |
| [0066](0066-agents-work-from-reviewed-specifications.md) | The coder works from reviewed requirements, contracts and tests. The reviewer decides their changes and tries to break each contract | decided |
| [0067](0067-a-sequence-stays-constant-because-the-gate-passed.md) | A sequence stays constant across a call because the gate passed the file. A bound name is an integer | decided |
| [0068](0068-cplusp-prove-and-its-diagnostics.md) | cplusp prove runs the gate, the translator and Dafny, and names each failed obligation at its C++ line with its contract line and assumptions | decided |
| [0069](0069-prove-trusts-only-a-finished-run-and-the-teams-gate.md) | prove trusts only a finished run of Dafny, runs the team's gate, and gives each obligation its own line and assumptions | decided |
| [0070](0070-a-finished-run-must-succeed-spans-keep-their-length.md) | A run of Dafny must finish and succeed. A span keeps a fixed length. A sequence passes to a sequence parameter | decided |
| [0071](0071-requirements-and-incremental-proofs.md) | Requirements and contracts come first. Check composition early, then implement and prove increments. Keep conditional obligations visible | decided |
| [0072](0072-recursion-and-the-order-of-slice-five.md) | Recursion with a decreases line on the function. The order of the fifth slice | decided |
| [0073](0073-structs-of-scalars-are-datatypes.md) | A struct of scalars is a Dafny datatype. Field reads in code and contracts, braced values, copies | decided |
| [0074](0074-a-mutable-reference-to-a-struct-has-no-rule-yet.md) | A non-const reference to a struct has no rule yet | decided |
| [0075](0075-an-optional-scalar-is-a-dafny-option.md) | An optional scalar is a Dafny Option. has_value, value and the dereference read it. Dafny proves each read | decided |
| [0076](0076-structs-that-hold-sequences-and-recursive-structs.md) | Structs that hold sequences, and recursive structs. Each sequence is a Vec, a seq with its bound on the length | decided |
| [0077](0077-move-the-shells-decisions-into-the-core.md) | Move the decisions of the shell into the core: the verdict of prove first, then the printer and the lexer | decided |
| [0078](0078-subspan-and-empty.md) | subspan with one argument and empty. Dafny proves the offset is in range | decided |
| [0079](0079-specification-functions-come-from-a-companion-file.md) | Specification functions come from a companion Dafny file of functions and predicates only. prove refuses an axiom in it | decided |
| [0080](0080-the-companion-file-is-checked-word-by-word-and-prove-counts-its-methods.md) | The companion file is checked against a list of keywords as Dafny reads it. prove counts the methods that Dafny verified, and names a resolution error | decided |
| [0081](0081-the-review-falls-back-to-opus.md) | The review falls back to Opus when Fable is not available | decided |

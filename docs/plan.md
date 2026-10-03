# cplusp: Verified C++ for LLM-Written Code — Implementation Plan

Oct 3, 2026 · Matthew Varendorff. Revised the same day after the first planning session; the changes are listed at the end.

## Goal and scope

The goal is that LLM-written C++ changes cannot introduce bugs. We prove the functions the LLM writes, not the codebase.

**Name:** the subset and its tooling are called **cplusp**, shown as **C+P** in prose: C++ with one plus removed, plus proof. Machines see `cplusp`: the repo, the CLI, `cplusp-*` checks, the `CPLUSP_*` markers and `cplusp-policy.yaml`.

**Who it is for.** The tool exists for the LLM coding loop first. The bot writes code, runs `cplusp` as a command, reads what comes back, and fixes it. Nothing runs automatically on save; the bot runs the processes itself. CI runs the same command as a backstop, so a PR cannot merge with a verified function that is not proved.

- **In scope:** functions the LLM writes or marks verified, checked against contracts for everything they call.
- **Trusted, not proven:** the core language, the standard library, the allocator, and any existing function given a contract. Each is described by a reviewed contract instead of a proof.
- **Plain:** existing code with no contract. Untouched until someone gives it a contract.
- **Out of scope:** finding bugs already in existing code.

Most LLM bugs are misuse of trusted parts: indexing past `size()`, holding a reference across `push_back`, overflow, off-by-one, dangling references. So trusted contracts must carry preconditions and invalidation rules, not just the happy path.

## Design principles

We are learning as we go, so the design has to survive being wrong.

- **The rule list is a living list.** Every row in the subset table is one entry in `cplusp-policy.yaml`. Adding a construct means adding an entry, pointing it at a check, and writing its sample pair. Removing one means deleting the entry. Nothing else changes.
- **Rules are independent.** A rule is one policy entry, one check, one sample pair and one message. Rules do not know about each other, so any one can be added, changed or dropped alone.
- **Pieces are swappable.** The gate, the driver, the translator and the prover sit behind narrow interfaces: the gate emits findings, the driver emits the verified set, the translator emits prover input, the prover emits pass or fail with locations. Any one can be replaced without touching the others. The prover in particular is expected to be swapped at least once.
- **Decisions are drafts.** Every Decision in the table and every default in this doc is the current best guess. The sample pairs are the regression net that makes changing them safe.

## Vocabulary

Two words that sound alike and mean different things. The tool uses them literally in its messages.

- **Provable.** Decided by the gate, before any proof runs. A function is provable when all three hold: it is in the verified set; its body uses only C+P features; and everything it calls has a contract. Known instantly.
- **Proved.** Decided by the prover, after it runs. The function meets its contract and cannot crash, overflow, index out of range or read uninitialised memory. Known only when the proof goes through.

Provable does not guarantee proved. A provable function can still fail its proof because it has a real bug, because its contract assumes too little or promises too much, or because the prover runs out of time.

The bot therefore hears two kinds of "no":

```
Not provable: pointer arithmetic is not allowed in verified code. Use std::span.
Not proved:   cannot show a + b fits in int32_t. Add a precondition, widen the type, or check first.
```

### Three kinds of function

| Kind | Gate | Proof | Contract | Callable from verified code |
| --- | --- | --- | --- | --- |
| **Verified** | Yes | Yes | Optional. Without one, the built-in promise still has to be proved: no crash, no overflow, no out-of-bounds, no uninitialised read | Yes |
| **Trusted** | Only the rows not marked Trusted only | No | Required, with a reason for skipping the proof | Yes |
| **Plain** | No | No | None | **No** |

The last column is the rule that holds the design together: verified code may only call things that have a contract. A verified function that needs an existing plain function gets a contract written for it, which promotes it to trusted. That is how the verified part grows into an old codebase, one function at a time.

**Membership, proposed default.** A function the bot writes from scratch is verified unless the bot says otherwise. An existing function the bot edits keeps whatever it was. The bot may mark a function trusted or plain with a one-line reason and carry on; the design pushes toward provable but never forces an old function to be proved because it was touched.

## Architecture

The gate runs first and decides whether the prover is even allowed to look. The gate is syntactic and fast; the prover is semantic and slow, so the gate rejects cheaply and the prover only ever sees code inside the subset.

```
bot edits code
  → cplusp gate     which functions are in the verified set?  are they provable?
  → cplusp prove    for each provable function: translate, prove against its contract
  → messages back   "Not provable: …" / "Not proved: …" / "verified: 3 functions"
  → bot fixes, reruns
CI runs the same command on the PR and blocks on any verified function that is not proved.
```

**Proofs chain through contracts.** Each function is proved once, alone, against its own contract. When it calls something, the proof uses only the callee's contract, never its body. The proof of a program is a chain of per-function proofs, each link resting on the next one's contract, bottoming out at trusted contracts for the standard library and existing code. Two consequences:

- "Prove the diff" falls out for free. The bot's new function is proved alone; nothing else is re-proved.
- Changing a contract is the expensive edit. If a function's contract changes, every caller must be re-proved, and the verified region for that run grows to include them. The tool tracks this.

**Exceptions are visible, not blocked.** Every run lists the trusted and plain markers in the change, with their reasons. The PR summary shows the counts: "12 verified, 2 trusted, 1 plain". Whether new markers need a human approval before merge is an open question; the proposed default is report only.

## No undefined behaviour in verified code

A verified function has no undefined behaviour, ever. The two stages split the work:

- **UB that lives in the construct** is the gate's job. The code is wrong whatever values flow through it, or it blinds the prover so that nothing after it can be proved. Reinterpret casts, unions used for punning, pointer arithmetic, C-style casts, `[[assume]]` and `unreachable`, reading a variable that was never initialised. Banned or trusted-only, caught instantly.
- **UB that depends on values** is the prover's job. Signed overflow, division by zero, shifting too far, indexing past the end, following a null or dangling reference. Good-looking code that is only wrong for some inputs. This is the built-in promise every verified function has to prove.

The Stage column in the table below records which stage guarantees each row.

## Canonical safe-C++ subsets

There is no single canonical subset; there are five that matter, each built for a different goal. Ours differs from all of them: the prover checks bounds and arithmetic, so we ban less than safety standards do.

| Source | Goal | What we take from it |
| --- | --- | --- |
| [MISRA C++:2023](https://www.parasoft.com/blog/misra-cpp-2023-guide/) | Safety-critical coding standard for C++17; 179 guidelines. Supersedes AUTOSAR C++14 after the 2019 merger | Construct bans (goto, unions, bit-fields, virtual inheritance, dynamic memory as advisory) and the mandatory / required / advisory deviation model |
| [C++ Core Guidelines profiles](https://wrocpp.github.io/toolset/memory-safety-cpp26-and-beyond/) | Bounds, type and lifetime safety; already implemented as clang-tidy `cppcoreguidelines-pro-*` checks | Type rules (casts, unions, varargs) as-is. Bounds rules mostly dropped: we prove indices instead of banning them |
| C++ safety profiles ([P3081](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p3081r2.pdf), P3589, P3984) | Language-level `[[profiles::enforce]]`; deferred to C++29 | The enforce / suppress attribute shape for our markers, so we can migrate later |
| [eCv++](http://www.eschertech.com/product_documentation/ecvReference/eCv_07_CPlusPlus.html) | The only shipped deductive verifier for a C++ subset (C++98/11) | Verification-driven restrictions: single inheritance, `final`, `override`, explicit constructors, no hiding, strict overloading |
| [VeriFast C++](https://arxiv.org/abs/2212.13754) | Deductive verifier with a C++ frontend | Hard limits to design around: templates were the main missing feature; no virtual base classes. No longer the primary prover candidate; see Tech stack |

Two data points support subsetting in practice. Apple's [P4158](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2026/p4158r0.pdf) reports hardening 4M lines of WebKit by subsetting. C++26 also standardised a hardened standard library, which complements but does not replace proofs.

## Candidate subset

The Decision column is the current draft; change any row and the gate config follows it. The list itself is open: rows will be added and removed as we learn, by the recipe under Phase 1. The biggest departure from safety standards: variable indexing and arithmetic are allowed, because the prover proves them safe instead of banning them.

- **Allow:** usable in verified code.
- **Restrict:** usable with the stated limit, enforced by a check.
- **Trusted only:** only inside trusted functions, behind a contract.
- **Ban:** rejected everywhere in verified code.

Stage says which part guarantees the row: **Gate** rejects the construct, **Prover** proves each use safe, **Spec** means a trusted contract carries the rules, and a dash means nothing to enforce.

| Area | Construct | Canonical stance | Why, for us | Decision | Stage |
| --- | --- | --- | --- | --- | --- |
| Types | Fixed-width ints, `bool`, `enum class` | MISRA prefers sized types and scoped enums | Easy for the prover | Allow | — |
| Types | Unscoped `enum` | MISRA: use scoped | Implicit int conversion | Ban | Gate |
| Types | Floating point | Allowed by all | Solvers are slow on floats; treat values as opaque, prove no NaN/inf only where specced | Restrict | Prover |
| Types | Unions | Banned by MISRA and Core Guidelines | Type punning breaks the memory model | Ban | Gate |
| Types | Bit-fields | MISRA advisory ban | Layout is implementation-defined | Trusted only | Gate |
| Types | Uninitialised variables | MISRA and Core Guidelines ban | Reading them is UB | Ban | Gate |
| Arithmetic | Signed/unsigned arithmetic, shifts, division | Allowed with care | Prover proves no overflow, bad shift or divide-by-zero | Allow | Prover |
| Arithmetic | Narrowing `static_cast` | Allowed if explicit | Prover proves the value fits | Allow | Prover |
| Memory | Non-owning raw pointer to one object | Core Guidelines allow as observer | Nullability goes in the contract | Restrict | Spec, Prover |
| Memory | Pointer arithmetic, array-to-pointer decay | Core Guidelines bounds profile ban | Use `std::span` instead | Ban | Gate |
| Memory | `new` / `delete`, `malloc` / `free` | MISRA advisory ban | Allocation is trusted; ownership goes through RAII types | Trusted only | Gate |
| Memory | `memcpy`, `memset`, `memmove` on anything but plain bytes | Core Guidelines discourage | Bypasses the type model; UB on non-trivial types | Trusted only | Gate |
| Memory | `std::launder`, placement `new` | Rare in application code | Object-lifetime games the prover cannot follow | Trusted only | Gate |
| Memory | `std::unique_ptr` | Recommended | Trusted contract; simple single ownership | Allow | Spec |
| Memory | `std::shared_ptr` | Allowed | Shared ownership and refcounts are hard to reason about | Trusted only | Gate |
| Memory | Lvalue references | Allowed | Modelled as pointers by the prover | Allow | Prover |
| Memory | Rvalue refs and `std::move` | Allowed | Prover support to confirm in the first slice | Restrict | Gate, Prover |
| Memory | Returning a reference or pointer to a local | MISRA mandatory ban | Always a bug | Ban | Gate |
| Library | `std::array`, `std::span` | Recommended | Core trusted types | Allow | Spec |
| Library | `std::vector`, `std::string`, maps | Allowed | Trusted contracts; no reference or iterator held across a mutation | Restrict | Spec |
| Library | `operator[]` with a variable index | Core Guidelines bounds profile ban | Prover proves the index is in range | Allow | Prover |
| Library | Iterators | Allowed | Range-for only; no iterator arithmetic | Restrict | Gate |
| Library | `std::optional`, `std::expected`, `std::variant` | Recommended | Trusted contracts; replaces unions and exceptions | Allow | Spec |
| Library | `<algorithm>` with lambdas | Allowed | Each algorithm needs a trusted contract; start with a short list | Restrict | Spec |
| Casts | C-style casts | Banned by MISRA and Core Guidelines | Hides what kind of cast it is. All forms, including plain numeric narrowing | Ban | Gate |
| Casts | `reinterpret_cast`, `const_cast` | Banned | Defeats the type model; most forms are UB. Message points to `std::bit_cast` | Trusted only | Gate |
| Casts | Downcasts (`static_cast`, `dynamic_cast`) | Core Guidelines ban `static_cast` downcasts | Use virtual dispatch | Ban | Gate |
| Classes | Classes, constructors, destructors, RAII | Allowed | Core of the subset | Allow | Prover |
| Classes | Single inheritance, `virtual`, `override`, `final` | eCv++ requires `override`, encourages `final` | Overrides checked for Liskov substitution | Allow | Prover |
| Classes | Multiple inheritance | eCv++: interfaces only | Keep the object model simple | Restrict | Gate |
| Classes | Virtual inheritance | MISRA advisory ban | Not provable today | Ban | Gate |
| Classes | Operator overloading | eCv++: const, no side effects | Pure operators only | Restrict | Gate |
| Classes | Implicit conversions (non-`explicit` ctors, conversion operators) | eCv++ requires `explicit` | Hidden calls confuse contracts | Ban | Gate |
| Classes | `mutable` members | eCv++ ban | Breaks `const` reasoning | Ban | Gate |
| Templates | Function and class templates | eCv++: type params only, no specialisation | Verified per instantiation | Restrict | Gate |
| Templates | `constexpr`, `consteval`, concepts | Allowed | Compile-time only | Allow | — |
| Templates | SFINAE, template metaprogramming | Discouraged | Nothing to prove at runtime, but unreadable contracts | Trusted only | Gate |
| Control | Exceptions | eCv++ ban; common in safety code | Use `std::expected`; verified code is `noexcept` | Ban | Gate |
| Control | `goto` | MISRA ban | No benefit | Ban | Gate |
| Control | `[[assume]]`, `__builtin_unreachable`, `std::unreachable` | New in C++23 | UB if the claim is false. Claims belong in the contract, where they are proved | Ban | Gate |
| Control | `setjmp` / `longjmp` | MISRA ban | Skips destructors; UB in C++ | Ban | Gate |
| Control | Recursion | MISRA ban | Needs a termination measure; loops are easier | Restrict | Gate, Prover |
| Control | Lambdas | Allowed | Only passed to trusted algorithms; no escaping reference captures | Restrict | Gate |
| Control | Function pointers, `std::function` | eCv++ allows with contracts | Indirect calls need contracts on the target | Trusted only | Gate |
| Control | Varargs, coroutines | Banned by Core Guidelines (varargs) | Not provable | Ban | Gate |
| Concurrency | Threads, atomics, mutexes | Allowed in MISRA | Concurrent proofs are far harder; isolate | Trusted only | Gate |
| Concurrency | `volatile` | MISRA restricts | Hardware access only | Trusted only | Gate |
| State | Globals, statics, member state | MISRA restricts globals | Allowed, but must appear in the frame of the contract | Restrict | Spec |
| Platform | Inline asm, SIMD intrinsics | MISRA restricts asm | Hot-path code goes behind a contract | Trusted only | Gate |
| Platform | Function-like macros | MISRA advisory ban | Hides code from the prover | Ban | Gate |

## Markers and the escape hatch

Three markers, proposed. They are the only way a function changes kind.

```cpp
#ifdef __clang__
  #define CPLUSP_VERIFIED       [[clang::annotate("cplusp:verified")]]
  #define CPLUSP_TRUSTED(why)   [[clang::annotate("cplusp:trusted", why)]]
  #define CPLUSP_PLAIN(why)     [[clang::annotate("cplusp:plain", why)]]
  #define CPLUSP_ASSUME(why)    [[clang::annotate("cplusp:assume", why)]]
#else
  #define CPLUSP_VERIFIED
  #define CPLUSP_TRUSTED(why)
  #define CPLUSP_PLAIN(why)
  #define CPLUSP_ASSUME(why)
#endif

CPLUSP_TRUSTED("AVX2 intrinsics")
int64_t fast_sum(std::span<const int64_t> a);
//@ requires ...;
//@ ensures  ...;
```

- `CPLUSP_VERIFIED` promotes an existing function into the verified set. New functions need no marker; they are verified by default.
- `CPLUSP_TRUSTED(why)` keeps a contract and skips the proof. Its body is unchecked for the Trusted only rows; its contract is still enforced on every caller.
- `CPLUSP_PLAIN(why)` opts a new function out entirely. Verified code cannot call it.
- `CPLUSP_ASSUME(why)` covers a single statement, such as one `reinterpret_cast` in an otherwise provable function.

`clang::annotate` survives into the AST (verified on clang 18, including the reason string), so the gate and the prover both see it. GCC builds compile it away.

Rules the gate enforces:

1. **A trusted function has a contract.** Without one, callers cannot be checked against it. "Not provable: `fast_sum` is trusted but has no contract."
2. **A reason is required.** Trusted, plain and assume markers must carry a non-empty string.
3. **Exceptions are reported, not hidden.** Each run prints the verified / trusted / plain counts for the change, with reasons, and the change from the base branch. Whether a human must approve new trusted or plain markers before merge is open; the bot is never blocked by it in the loop.
4. **Verified code calls only contracted code.** A call from a verified function to a plain one is a gate failure naming the callee: "Not provable: calls `legacy_parse`, which has no contract. Give it one to make it trusted."

The marker names mirror C++29's planned `[[profiles::suppress]]`, so we can switch to the standard attribute if profiles land.

## Phase 0: the thin slice

The first thing to exist is the whole pipeline, tiny, end to end, the way `dafny verify` feels. Not the gate on its own.

1. One C++ function with a contract. The bot runs `cplusp verify file.cpp` and gets back `verified: 1 function`.
2. Two functions, one calling the other. The caller's proof uses the callee's contract. Change the callee's contract and watch the caller get re-proved.
3. Break one. Remove a precondition and get `Not proved: cannot show the result fits in int32_t`. Add a `goto` and get `Not provable: goto is not allowed in verified code`.

Exit test: all three run from one command with messages a bot can act on without reading anything else. This settles the prover choice, the spec syntax and the shape of the messages before any breadth is built.

## Phase 1: the gate

The gate is a clang-tidy module that rejects any verified function using a banned construct, plus a driver that works out the verified set and shapes the messages. About half the rules reuse existing checks; the rest are short AST-matcher checks.

**Design choices**

- **A separate run, alongside existing team configs.** The gate invokes clang-tidy with its own generated config, its own loaded plugin, and the team's `compile_commands.json`. The team's `.clang-tidy` is never read or edited, and their normal lint run is unchanged. The gate fails only on policy rows, so team settings cannot add noise or silently switch our checks off.
- **Versions decoupled.** The gate brings its own pinned clang-tidy, so teams on clang-tidy 16 through 20 are unaffected. The plugin also builds from source against LLVM 17 to 20 for teams that want it in their editor. A team's own loaded plugins coexist with ours.
- **Function granularity.** The unit is a function, never a file. The driver maps uncommitted edits to enclosing functions, applies the membership default, and adds callers of any function whose contract changed.
- **Policy file drives checks.** `cplusp-policy.yaml` mirrors the Decision column, one line per row. The driver emits the clang-tidy config from it, so changing a decision needs no code change.
- **Messages are written for the bot.** Every finding says what it is, why the row bans it, and what to use instead, taken from the table. The prefix is always `Not provable:`.
- **Trusted scopes.** Diagnostics for Trusted only rows are dropped inside trusted functions after the run; everything else stands.
- **Syntactic only.** The gate bans constructs; it does not reason about values. "Reference held across `push_back`" is the prover's job, via the trusted `vector` contract.
- **One sample pair per row.** Each row gets an `allowed.cpp` and a `banned.cpp`. The pair proves the chosen check means what the row says, and doubles as the test suite. The first two rows checked already disagreed with the doc; see the table below.

**Adding or removing a rule**

1. Add a row to the table and an entry to `cplusp-policy.yaml`: construct, decision, why, use instead.
2. Point it at a check: an upstream clang-tidy check if one means exactly what the row says, otherwise a new `cplusp-*` check of a few dozen lines.
3. Write the sample pair, `allowed.cpp` and `banned.cpp`. The pair is the proof that the check means what the row says.
4. Run the suite. Nothing else changes.

Removing a rule is deleting the entry and its pair. Changing a decision is editing one word.

**Existing checks to enable**

| Construct | Check | Note |
| --- | --- | --- |
| C-style casts | `google-readability-casting` | Verified: `cppcoreguidelines-pro-type-cstyle-cast` only flags casts between unrelated types, downcasts and const-dropping. `(int)big` passes it. The google check flags every C-style cast |
| `reinterpret_cast`, `const_cast` | `cppcoreguidelines-pro-type-reinterpret-cast`, `cppcoreguidelines-pro-type-const-cast` | |
| Downcasts | `cppcoreguidelines-pro-type-static-cast-downcast` | |
| Unions | `cppcoreguidelines-pro-type-union-access` plus custom `cplusp-union-decl` | The upstream check fires on member access only, not on the declaration |
| Varargs | `cppcoreguidelines-pro-type-vararg` | |
| Uninitialised variables | `cppcoreguidelines-init-variables`, `cppcoreguidelines-pro-type-member-init` | |
| Pointer arithmetic, decay | `cppcoreguidelines-pro-bounds-pointer-arithmetic`, `cppcoreguidelines-pro-bounds-array-to-pointer-decay` | |
| `new` / `delete`, `malloc` | `cppcoreguidelines-owning-memory`, `cppcoreguidelines-no-malloc` | |
| `goto` | `cppcoreguidelines-avoid-goto` | |
| Recursion | `misc-no-recursion` | |
| Inline asm | `hicpp-no-assembler` | |
| Function-like macros | `cppcoreguidelines-macro-usage` | |
| Implicit constructors | `google-explicit-constructor` | |
| Missing `override` | `modernize-use-override` | |

Deliberately **not** enabled: `cppcoreguidelines-pro-bounds-constant-array-index` and `cppcoreguidelines-pro-bounds-avoid-unchecked-container-access`. They ban variable indexing, which we prove instead.

**Custom checks to write**

- `cplusp-unscoped-enum`, `-union-decl`, `-bitfield`, `-mutable`
- `-virtual-inheritance`, `-multiple-inheritance` (allow only pure-interface bases)
- `-exceptions` (`throw`, `try`; verified functions must be `noexcept`)
- `-shared-ptr`, `-iterator-arithmetic`, `-conversion-operator`, `-impure-operator`
- `-function-pointer`, `-coroutine`, `-concurrency` (`<thread>`, `<atomic>`, `<mutex>` use), `-volatile`, `-intrinsics`
- `-unreachable-assume` (`[[assume]]`, `__builtin_unreachable`, `std::unreachable`), `-longjmp`, `-raw-memory-ops` (`memcpy` and friends on non-byte types), `-launder-placement-new`
- `-template-specialization`
- `-markers` (trusted has a contract, reasons non-empty, no verified-to-plain calls)
- `-index` (emits every function's range and kind in the same run, so the driver needs no second parse)

**Delivery**

- [ ] Phase 0 thin slice: one function verified end to end, two chained, one broken each way
- [ ] Plugin skeleton: builds, loads, lists its checks; one custom check with its sample pair
- [ ] Policy YAML schema and the config it emits; golden test
- [ ] `-markers` and `-index`; driver maps edits to functions and filters by kind
- [ ] Remaining custom checks, one sample pair each; upstream checks verified row by row
- [ ] Messages tuned on the bot: what, why, use instead
- [ ] CI job running the same command: fail on violation, SARIF for PR annotations, verified / trusted / plain delta
- [ ] Decide and, if yes, add the approval rule for new trusted and plain markers
- [ ] Run on 3–5 real hot-path files; tune decisions from the noise

## Tech stack

Provisional. Parked as "maybe" where the first slice does not need a decision; stated where it does.

| Piece | Choice | Status |
| --- | --- | --- |
| Gate checks and index | C++20 clang-tidy module. CMake and Ninja. LLVM 18 pinned, builds against 17 to 20 | Forced: a clang-tidy module can only be C++ |
| Driver `cplusp` | Rust. No Python anywhere. TypeScript not in the core | Preferred |
| Prover | Dafny underneath, with the gated C++ translated to it and errors mapped back to C++ lines. The translator is the new trusted component, tested by compiling the Dafny and running both on the same inputs | Proposed, pending the thin slice |
| Prover, plan B | Verus, via translation to Rust. Exact machine ints and fast, but translated C++ must satisfy the borrow checker | Fallback |
| Prover, dropped | VeriFast directly on C++. Immature frontend, thin LLM familiarity | Not primary |
| Spec syntax in C++ | `//@ requires` / `//@ ensures` comments with Dafny-flavoured expressions, carried through by the translator | Open |
| Check tests | Rust runner over the sample pairs, reading `// CHECK-MESSAGES` lines | Preferred |
| Bot integration | A skill tells the bot to run `cplusp verify` after writing C++ and to act on the messages. No automatic hook | Decided |

## Later phases and open questions

| Phase | Delivers | Exit test |
| --- | --- | --- |
| 0. Thin slice | One command, one function, gate plus proof, messages a bot can act on | Three runs above pass; prover and spec syntax settled |
| 1. Gate | Every row enforced with a sample pair; policy file; driver; CI backstop | Runs on 3–5 real hot-path files with tolerable noise |
| 2. Trusted base | Contracts for `std::array`, `span`, `vector`, `optional`, `expected`, `unique_ptr`, plus existing-code contracts | Phase 0 functions verify against library contracts, not stubs |
| 3. LLM loop | A skill drives generate, run `cplusp verify`, repair on the message; bounded checker as a fallback for counterexamples | The bot verifies most new functions without human edits |

**Open questions**

- Does the translator route hold up on templates and rvalue references? The thin slice decides the Templates and move rows.
- Spec syntax: `//@` comments with Dafny-flavoured expressions, or macros that can later emit C++26 `pre` / `post`?
- Must a human approve new trusted or plain markers before merge, or is reporting enough?
- Is "new functions are verified by default, edited functions keep their kind" the right membership rule?
- Which clang-tidy versions do the teams run, and are their builds GCC-based? Sets the build matrix and any flag shims.
- Concurrency is Trusted only. Acceptable for the hot path, or do we need a lock-free subset later?
- Floating point: are value-level properties ever needed, or is opaque enough?
- Who owns and reviews the trusted contract library?

## Changes in this revision

- Added design principles: the rule list is living, rules are independent, pieces are swappable, decisions are drafts. Added the recipe for adding or removing a rule.
- Positioned the tool for the LLM coding loop first, run on demand by the bot. CI is a backstop running the same command. No automatic hook.
- Added the vocabulary: provable is decided by the gate before any proof, proved by the prover after. Messages use the two words as prefixes.
- Added the three kinds of function, verified, trusted and plain, and the rule that verified code calls only contracted code. The bot may mark exceptions with a reason.
- Added the proposed membership default: new functions verified unless marked, edited functions keep their kind.
- Added the principle that verified code has no undefined behaviour, split between gate and prover, and a Stage column recording which stage guarantees each row.
- Added rows: `memcpy` family and `std::launder` / placement new as Trusted only; `[[assume]]` / `unreachable` and `setjmp` / `longjmp` as Ban.
- Swapped the C-style cast check to `google-readability-casting` after the named check let a narrowing cast through. Noted that the union check fires on access only.
- Made the first step a thin end-to-end slice instead of the gate alone.
- Recorded that the gate runs separately from, and never edits, a team's existing clang-tidy config, with its own pinned clang-tidy.
- Replaced VeriFast as the primary prover with Dafny via translation, provisional on the thin slice. Verus is plan B.
- Added a provisional tech stack: C++ only for the clang-tidy module, Rust for the rest, no Python.

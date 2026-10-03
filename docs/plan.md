# cplusp: Verified C++ for LLM-Written Code — Implementation Plan

Oct 3, 2026 · Matthew Varendorff. Revised the same day after the first planning session. The last section lists the changes.

## Goal and scope

The goal is that LLM-written C++ changes cannot introduce bugs. We prove the functions the LLM writes, not the codebase.

**Name:** we call the subset and its tooling **cplusp**, shown as **C+P** in prose: C++ with one plus removed, plus proof. Machines see `cplusp`: the repo, the CLI, `cplusp-*` checks, the `CPLUSP_*` markers and `cplusp-policy.yaml`.

**Who it is for.** The tool exists for the LLM coding loop first. The bot writes code, runs `cplusp` as a command, reads what comes back, and fixes it. Nothing runs automatically on save. The bot runs the processes itself. CI runs the same command as a backstop, so a PR cannot merge with a verified function that is not proved.

- **In scope:** functions the LLM writes or marks verified, checked against contracts for everything they call.
- **Trusted, not proven:** the core language, the standard library, the allocator, and any existing function that has a contract. A reviewed contract describes each one instead of a proof.
- **Plain:** existing code with no contract. It stays untouched until someone gives it a contract.
- **Out of scope:** finding bugs already in existing code.

Most LLM bugs are misuse of trusted parts: indexing past `size()`, holding a reference across `push_back`, overflow, off-by-one, dangling references. So trusted contracts must carry preconditions and invalidation rules, not just the happy path.

## Design principles

We are learning as we go, so the design has to survive being wrong.

- **The rule list is a living list.** Every row in the subset table is one entry in `cplusp-policy.yaml`. To add a construct, add an entry, point it at a check, and write its sample pair. To remove a construct, remove its entry. Nothing else changes.
- **Rules are independent.** A rule is one policy entry, one check, one sample pair and one message. Rules do not know about each other, so you can add, change or drop any one alone.
- **Pieces are swappable.** The gate, the driver, the translator and the prover have narrow interfaces. The gate emits findings. The driver emits the verified set. The translator emits prover input. The prover emits pass or fail with locations. You can replace any one without touching the others. We expect to swap the prover at least once.
- **Decisions are drafts.** Every Decision in the table and every default in this doc is the current best guess. The sample pairs are the regression net that makes changing them safe.

## Vocabulary

Two words that sound alike and mean different things. The tool uses them literally in its messages.

- **Provable.** The gate decides this before any proof runs. A function is provable when all three hold:
  1. It is in the verified set.
  2. Its body uses only C+P features.
  3. Everything it calls has a contract.

  The gate knows this instantly.
- **Proved.** The prover decides this after it runs. The function meets its contract. It cannot crash, overflow, index out of range or read uninitialised memory. The tool knows this only when the proof goes through.
- **Contract.** The `//@ requires`, `//@ ensures` and related lines on a function. Other tools call this a spec or a VeriFast definition. The syntax is open. The examples below show the shape, not the final grammar.

Provable does not guarantee proved. A provable function can still fail its proof. Three causes:

- It has a real bug.
- Its contract assumes too little or promises too much.
- The prover runs out of time.

The bot therefore hears two kinds of "no":

```
Not provable: pointer arithmetic is not allowed in verified code. Use std::span.
Not proved:   cannot show a + b fits in int32_t. Add a precondition, widen the type, or check first.
```

### Three kinds of function

| Kind | Gate | Proof | Contract | Callable from verified code |
| --- | --- | --- | --- | --- |
| **Verified** | Yes | Yes | Optional. Without one, the prover still checks the built-in promise: no crash, no overflow, no out-of-bounds, no uninitialised read | Yes |
| **Trusted** | Only the rows not marked Trusted only | No | Required, with a reason for skipping the proof | Yes |
| **Plain** | No | No | None | **No** |

The last column is the rule that holds the design together: verified code may only call things that have a contract. If a verified function needs an existing plain function, the bot writes a contract for that function. The contract promotes it to trusted. That is how the verified part grows into an old codebase, one function at a time.

**Membership, proposed default.** A function the bot writes from scratch is verified unless the bot says otherwise. An existing function the bot edits keeps its kind. The bot may mark a function trusted or plain with a one-line reason and continue. The design pushes toward provable. It never forces an old function to be proved because the bot touched it.

## Architecture

The gate runs first and decides whether the prover may look at the code at all. The gate is syntactic and fast. The prover is semantic and slow. So the gate rejects cheaply, and the prover only ever sees code inside the subset.

```
bot edits code
  → cplusp gate     which functions are in the verified set?  are they provable?
  → cplusp prove    for each provable function: translate, prove against its contract
  → messages back   "Not provable: …" / "Not proved: …" / "verified: 3 functions"
  → bot fixes, reruns
CI runs the same command on the PR and blocks on any verified function that is not proved.
```

**Proofs chain through contracts.** The prover proves each function once, alone, against its own contract. When the function calls something, the proof uses only the callee's contract, never its body. The proof of a program is a chain of per-function proofs. Each link rests on the next one's contract. The chain ends at trusted contracts for the standard library and existing code. Two consequences:

- "Prove the diff" comes for free. The prover proves the bot's new function alone. It re-proves nothing else.
- Changing a contract is the expensive edit. If a function's contract changes, the prover must re-prove every caller. The verified region for that run grows to include them. The tool tracks this.

**Exceptions are visible, not blocked.** Every run lists the trusted and plain markers in the change, with their reasons. The PR summary shows the counts: "12 verified, 2 trusted, 1 plain". Whether new markers need a human approval before merge is an open question. The proposed default is report only.

## No undefined behaviour in verified code

A verified function has no undefined behaviour, ever. The two stages split the work:

- **UB that lives in the construct** is the gate's job. The code is wrong whatever values flow through it. Or it blinds the prover so that nothing after it can be proved. Examples: reinterpret casts, unions used for punning, pointer arithmetic, C-style casts, `[[assume]]` and `unreachable`, reading a variable that was never initialised. The gate bans these or limits them to trusted code, and catches them instantly.
- **UB that depends on values** is the prover's job. Examples: signed overflow, division by zero, shifting too far, indexing past the end, following a null or dangling reference. This is good-looking code that is only wrong for some inputs. The prover must prove the built-in promise for every verified function.

The Stage column in the table below records which stage guarantees each row.

## Canonical safe-C++ subsets

There is no single canonical subset. Five matter, and each one serves a different goal. Ours differs from all of them: the prover checks bounds and arithmetic, so we ban less than safety standards do.

| Source | Goal | What we take from it |
| --- | --- | --- |
| [MISRA C++:2023](https://www.parasoft.com/blog/misra-cpp-2023-guide/) | Safety-critical coding standard for C++17 with 179 guidelines. It supersedes AUTOSAR C++14 after the 2019 merger | Construct bans (goto, unions, bit-fields, virtual inheritance, dynamic memory as advisory) and the mandatory / required / advisory deviation model |
| [C++ Core Guidelines profiles](https://wrocpp.github.io/toolset/memory-safety-cpp26-and-beyond/) | Bounds, type and lifetime safety. Already implemented as clang-tidy `cppcoreguidelines-pro-*` checks | Type rules (casts, unions, varargs) as-is. Bounds rules mostly dropped: we prove indices instead of banning them |
| C++ safety profiles ([P3081](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p3081r2.pdf), P3589, P3984) | Language-level `[[profiles::enforce]]`, deferred to C++29 | The enforce / suppress attribute shape for our markers, so we can migrate later |
| [eCv++](http://www.eschertech.com/product_documentation/ecvReference/eCv_07_CPlusPlus.html) | The only shipped deductive verifier for a C++ subset (C++98/11) | Verification-driven restrictions: single inheritance, `final`, `override`, explicit constructors, no hiding, strict overloading |
| [VeriFast C++](https://arxiv.org/abs/2212.13754) | Deductive verifier with a C++ frontend | Hard limits to design around: templates were the main missing feature, and it does not support virtual base classes. No longer the primary prover candidate. See Tech stack |

Two data points support subsetting in practice. Apple's [P4158](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2026/p4158r0.pdf) reports hardening 4M lines of WebKit by subsetting. C++26 also standardised a hardened standard library, which complements but does not replace proofs.

## Candidate subset

The Decision column is the current draft. Change any row and the gate config follows it. The list itself is open: we will add and remove rows as we learn, by the recipe under Phase 1. The biggest departure from safety standards: we allow variable indexing and arithmetic, because the prover proves them safe instead of banning them.

- **Allow:** usable in verified code.
- **Restrict:** usable only within the limit named in the Decision cell. A check or the contract enforces it.
- **Trusted only:** only inside trusted functions, behind a contract.
- **Ban:** rejected everywhere in verified code.

Stage says which part guarantees the row. **Gate** rejects the construct. **Prover** proves each use safe. **Spec** means a trusted contract carries the rules. A dash means there is nothing to enforce.

| Area | Construct | Canonical stance | Why, for us | Decision | Stage |
| --- | --- | --- | --- | --- | --- |
| Types | Fixed-width ints, `bool`, `enum class` | MISRA prefers sized types and scoped enums | Easy for the prover | Allow | — |
| Types | Unscoped `enum` | MISRA: use scoped | Implicit int conversion | Ban | Gate |
| Types | Floating point | Allowed by all | Solvers are slow on floats | Restrict: values are opaque to the prover. It proves no NaN or inf only where the contract says so | Prover |
| Types | Unions | Banned by MISRA and Core Guidelines | Type punning breaks the memory model | Ban | Gate |
| Types | Bit-fields | MISRA advisory ban | Layout is implementation-defined | Trusted only | Gate |
| Types | Uninitialised variables | MISRA and Core Guidelines ban | Reading them is UB | Ban | Gate |
| Arithmetic | Signed/unsigned arithmetic, shifts, division | Allowed with care | Prover proves no overflow, bad shift or divide-by-zero | Allow | Prover |
| Arithmetic | Narrowing `static_cast` | Allowed if explicit | Prover proves the value fits | Allow | Prover |
| Memory | Non-owning raw pointer to one object | Core Guidelines allow as observer | Nullability goes in the contract | Restrict: one object, no ownership, no arithmetic | Spec, Prover |
| Memory | Pointer arithmetic, array-to-pointer decay | Core Guidelines bounds profile ban | Use `std::span` instead | Ban | Gate |
| Memory | `new` / `delete`, `malloc` / `free` | MISRA advisory ban | Allocation is trusted. Ownership goes through RAII types | Trusted only | Gate |
| Memory | `memcpy`, `memset`, `memmove` on anything but plain bytes | Core Guidelines discourage | Bypasses the type model. UB on non-trivial types | Trusted only | Gate |
| Memory | `std::launder`, placement `new` | Rare in application code | Object-lifetime games the prover cannot follow | Trusted only | Gate |
| Memory | `std::unique_ptr` | Recommended | Trusted contract. Simple single ownership | Allow | Spec |
| Memory | `std::shared_ptr` | Allowed | Shared ownership and refcounts are hard to reason about | Trusted only | Gate |
| Memory | Lvalue references | Allowed | The prover models them as pointers | Allow | Prover |
| Memory | Rvalue refs and `std::move` | Allowed | Prover support to check in the first slice | Restrict: move locals and parameters only, no use after move | Gate, Prover |
| Memory | Returning a reference or pointer to a local | MISRA mandatory ban | Always a bug | Ban | Gate |
| Library | `std::array`, `std::span` | Recommended | Core trusted types | Allow | Spec |
| Library | `std::vector`, `std::string`, maps | Allowed | Trusted contracts carry the invalidation rules | Restrict: only methods that have a trusted contract, no reference or iterator held across a mutation | Spec |
| Library | `operator[]` with a variable index | Core Guidelines bounds profile ban | Prover proves the index is in range | Allow | Prover |
| Library | Iterators | Allowed | Iterator arithmetic is pointer arithmetic in disguise | Restrict: range-for only | Gate |
| Library | `std::optional`, `std::expected`, `std::variant` | Recommended | Trusted contracts. Replaces unions and exceptions | Allow | Spec |
| Library | `<algorithm>` with lambdas | Allowed | Each algorithm needs a trusted contract | Restrict: only algorithms on the trusted list, which starts short | Spec |
| Casts | C-style casts | Banned by MISRA and Core Guidelines | Hides what kind of cast it is. All forms, including plain numeric narrowing | Ban | Gate |
| Casts | `reinterpret_cast`, `const_cast` | Banned | Defeats the type model. Most forms are UB. Message points to `std::bit_cast` | Trusted only | Gate |
| Casts | Downcasts (`static_cast`, `dynamic_cast`) | Core Guidelines ban `static_cast` downcasts | Use virtual dispatch | Ban | Gate |
| Classes | Classes, constructors, destructors, RAII | Allowed | Core of the subset | Allow | Prover |
| Classes | Single inheritance, `virtual`, `override`, `final` | eCv++ requires `override`, encourages `final` | The prover checks overrides for Liskov substitution | Allow | Prover |
| Classes | Multiple inheritance | eCv++: interfaces only | Keep the object model simple | Restrict: extra bases must be pure interfaces | Gate |
| Classes | Virtual inheritance | MISRA advisory ban | Not provable today | Ban | Gate |
| Classes | Operator overloading | eCv++: const, no side effects | Hidden side effects confuse contracts | Restrict: const and free of side effects | Gate |
| Classes | Implicit conversions (non-`explicit` ctors, conversion operators) | eCv++ requires `explicit` | Hidden calls confuse contracts | Ban | Gate |
| Classes | `mutable` members | eCv++ ban | Breaks `const` reasoning | Ban | Gate |
| Templates | Function and class templates | eCv++: type params only, no specialisation | Verified per instantiation | Restrict: type parameters only, no specialisation | Gate |
| Templates | `constexpr`, `consteval`, concepts | Allowed | Compile-time only | Allow | — |
| Templates | SFINAE, template metaprogramming | Discouraged | Nothing to prove at runtime, but unreadable contracts | Trusted only | Gate |
| Control | Exceptions | eCv++ ban. Common in safety code | Use `std::expected`. Verified code is `noexcept` | Ban | Gate |
| Control | `goto` | MISRA ban | No benefit | Ban | Gate |
| Control | `[[assume]]`, `__builtin_unreachable`, `std::unreachable` | New in C++23 | UB if the claim is false. Claims belong in the contract, where the prover checks them | Ban | Gate |
| Control | `setjmp` / `longjmp` | MISRA ban | Skips destructors. UB in C++ | Ban | Gate |
| Control | Recursion | MISRA ban | The prover needs a termination measure. Loops are easier | Restrict: needs a `decreases` clause in the contract | Gate, Prover |
| Control | Lambdas | Allowed | Captured references can dangle | Restrict: passed directly to a trusted algorithm, no reference capture that escapes | Gate |
| Control | Function pointers, `std::function` | eCv++ allows with contracts | Indirect calls need contracts on the target | Trusted only | Gate |
| Control | Varargs, coroutines | Banned by Core Guidelines (varargs) | Not provable | Ban | Gate |
| Concurrency | Threads, atomics, mutexes | Allowed in MISRA | Concurrent proofs are far harder. Isolate them | Trusted only | Gate |
| Concurrency | `volatile` | MISRA restricts | Hardware access only | Trusted only | Gate |
| State | Globals, statics, member state | MISRA restricts globals | Hidden state breaks modular proofs | Restrict: listed in the contract's reads or modifies clause | Spec |
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

- `CPLUSP_VERIFIED` promotes an existing function into the verified set. New functions need no marker. They are verified by default.
- `CPLUSP_TRUSTED(why)` keeps a contract and skips the proof. The gate does not check its body against the Trusted only rows. The gate still enforces its contract on every caller.
- `CPLUSP_PLAIN(why)` opts a new function out entirely. Verified code cannot call it.
- `CPLUSP_ASSUME(why)` covers a single statement, such as one `reinterpret_cast` in an otherwise provable function.

`clang::annotate` survives into the AST, so the gate and the prover both see it. We checked this on clang 18, including the reason string. GCC builds compile it away.

Rules the gate enforces:

1. **A trusted function has a contract.** Without one, the gate cannot check callers against it. Message: "Not provable: `fast_sum` is trusted but has no contract."
2. **Every marker carries a reason.** Trusted, plain and assume markers must carry a non-empty string.
3. **The gate reports exceptions.** Each run prints the verified, trusted and plain counts for the change, with reasons, and the change from the base branch. Whether a human must approve new trusted or plain markers before merge is open. The loop never blocks the bot on it.
4. **Verified code calls only contracted code.** A call from a verified function to a plain one fails the gate. The message names the callee: "Not provable: calls `legacy_parse`, which has no contract. Give it one to make it trusted."

The marker names mirror C++29's planned `[[profiles::suppress]]`, so we can switch to the standard attribute if profiles land.

## Examples

Contracts use the proposed `//@` syntax with Dafny-flavoured expressions. `result` is the return value. `old(x)` is the value of `x` on entry. Quantifiers read as in Dafny: `forall i :: 0 <= i < n ==> P(i)`.

### A verified function with a contract

```cpp
//@ requires a.size() > 0
//@ requires forall i :: 0 <= i < a.size() ==> 0 <= a[i] <= 1000
//@ ensures  0 <= result <= 1000
int32_t mean(std::span<const int32_t> a) {
  int64_t total = 0;
  //@ invariant 0 <= total <= i * 1000
  for (size_t i = 0; i < a.size(); ++i) {
    total += a[i];
  }
  return static_cast<int32_t>(total / static_cast<int64_t>(a.size()));
}
```

The prover shows four things here. The index `a[i]` is in range, from the loop condition. `total` cannot overflow, from the invariant. The division has a non-zero divisor, from the first precondition. The narrowing cast fits, because the quotient is between 0 and 1000. None of these needs a runtime check.

### A caller that uses only the callee's contract

```cpp
//@ requires readings.size() > 0
//@ requires forall i :: 0 <= i < readings.size() ==> 0 <= readings[i] <= 1000
bool over_half(std::span<const int32_t> readings) {
  return mean(readings) > 500;
}
```

`over_half` has no `ensures` of its own, so the prover checks only the built-in promise. To prove the call, it shows that `mean`'s two preconditions follow from `over_half`'s. It never reads `mean`'s body. If `mean`'s contract changes, the prover re-proves `over_half`.

### What the bot hears when a proof fails

Remove the first precondition from `mean` and run again:

```
Not proved: mean, line 11: cannot show a.size() != 0 for the division. Add a precondition or check first.
```

Hold a reference across a mutation, the most common LLM bug in the doc's opening:

```cpp
//@ requires v.size() < 1'000'000
void append_twice(std::vector<int32_t>& v, int32_t x) {
  int32_t& first = v[0];
  v.push_back(x);
  first = x;
}
```

```
Not proved: append_twice, line 3: cannot show 0 < v.size() for v[0]. Add a precondition or check first.
Not proved: append_twice, line 5: `first` refers into v, and push_back on line 4 invalidated it.
```

The second message comes from the trusted contract for `vector`, not from any rule about references.

### What the bot hears when the gate rejects

```cpp
int32_t first_nonzero(const int32_t* p, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    if (*(p + i) != 0) return *(p + i);
  }
  return 0;
}
```

```
Not provable: first_nonzero, line 3: pointer arithmetic is not allowed in verified code. Use std::span.
```

The gate stops here. The prover never runs on this function.

### A trusted function

```cpp
CPLUSP_TRUSTED("AVX2 intrinsics, checked by hand against the scalar version")
//@ requires a.size() <= 1'000'000
//@ requires forall i :: 0 <= i < a.size() ==> -1'000'000 <= a[i] <= 1'000'000
//@ ensures  -1'000'000'000'000 <= result <= 1'000'000'000'000
int64_t fast_sum(std::span<const int64_t> a);
```

The gate skips the Trusted only rows inside `fast_sum`'s body. The prover never looks at it. Every caller is still checked against the two preconditions, and every caller may rely on the bound in `ensures`.

### An existing function promoted from plain to trusted

```cpp
// Body unchanged. The contract alone makes it callable from verified code.
CPLUSP_TRUSTED("existing parser, body unchanged, contract reviewed by the owning team")
//@ requires text.size() <= 65535
//@ ensures  result.has_value() ==> 0 <= *result <= 65535
std::optional<int32_t> legacy_parse(std::string_view text);
```

### A function the bot opts out

```cpp
CPLUSP_PLAIN("one-off migration, runs once under supervision")
void migrate_all(Database& db);
```

Verified code cannot call `migrate_all`. The run reports it: "1 plain: migrate_all, one-off migration, runs once under supervision".

### An excerpt of a trusted library contract

```cpp
// std::vector<T>, trusted contract, excerpt
//@ ensures size() == old(size()) + 1
//@ ensures (*this)[size() - 1] == x
//@ ensures forall i :: 0 <= i < old(size()) ==> (*this)[i] == old((*this)[i])
//@ invalidates all references and iterators into *this
void push_back(const T& x);

//@ requires 0 <= i < size()
T& operator[](size_t i);
```

The `invalidates` line is what produced the second `append_twice` message. Trusted contracts carry preconditions and invalidation rules, not just the happy path.

## Phase 0: the thin slice

The first thing to exist is the whole pipeline, tiny, end to end, the way `dafny verify` feels. Not the gate on its own.

1. One C++ function with a contract. The bot runs `cplusp verify file.cpp` and gets back `verified: 1 function`.
2. Two functions, one calling the other. The caller's proof uses the callee's contract. Change the callee's contract and watch the prover re-prove the caller.
3. Break one. Remove a precondition and get `Not proved: cannot show the result fits in int32_t`. Add a `goto` and get `Not provable: goto is not allowed in verified code`.

Exit test: all three run from one command, with messages a bot can act on without reading anything else. This settles the prover choice, the spec syntax and the shape of the messages before we build any breadth.

## Phase 1: the gate

The gate has two parts. A clang-tidy module rejects any verified function that uses a banned construct. A driver computes the verified set and shapes the messages. About half the rules reuse existing checks. The rest are short AST-matcher checks.

**Design choices**

- **A separate run, alongside existing team configs.** The gate invokes clang-tidy with its own generated config, its own loaded plugin, and the team's `compile_commands.json`. The gate never reads or edits the team's `.clang-tidy`. Their normal lint run does not change. The gate fails only on policy rows, so team settings cannot add noise or silently disable our checks.
- **Versions decoupled.** The gate brings its own pinned clang-tidy. Teams on clang-tidy 16 through 20 see no change. The plugin also builds from source against LLVM 17 to 20, for teams that want it in their editor. A team's own loaded plugins coexist with ours.
- **Function granularity.** The unit is a function, never a file. The driver maps uncommitted edits to enclosing functions and applies the membership default. It adds callers of any function whose contract changed.
- **Policy file drives checks.** `cplusp-policy.yaml` mirrors the Decision column, one entry per row. The driver emits the clang-tidy config from it, so a changed decision needs no code change. The file format is in [policy.md](policy.md).
- **Messages for the bot.** Every finding says what it is, why the row bans it, and what to use instead. The text comes from the table. The prefix is always `Not provable:`.
- **Trusted scopes.** After the run, the driver drops diagnostics for Trusted only rows inside trusted functions. Everything else stands.
- **Syntactic only.** The gate bans constructs. It does not reason about values. "Reference held across `push_back`" is the prover's job, via the trusted `vector` contract.
- **One sample pair per row.** Each row gets an `allowed.cpp` and a `banned.cpp`. The pair proves the chosen check means what the row says, and doubles as the test suite. The first two rows we checked already disagreed with the doc. See the table below.

**Adding or removing a rule**

1. Add a row to the table and an entry to `cplusp-policy.yaml`: construct, decision, why, use instead.
2. Point it at a check. Use an upstream clang-tidy check if one means exactly what the row says. Otherwise write a new `cplusp-*` check of a few dozen lines.
3. Write the sample pair, `allowed.cpp` and `banned.cpp`. The pair is the proof that the check means what the row says.
4. Run the suite. Nothing else changes.

To remove a rule, remove its entry and its pair. To change a decision, edit one word.

**Existing checks to enable**

| Construct | Check | Note |
| --- | --- | --- |
| C-style casts | `google-readability-casting` | Checked: `cppcoreguidelines-pro-type-cstyle-cast` only flags casts between unrelated types, downcasts and const-dropping. `(int)big` passes it. The google check flags every C-style cast |
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

We deliberately do **not** enable `cppcoreguidelines-pro-bounds-constant-array-index` or `cppcoreguidelines-pro-bounds-avoid-unchecked-container-access`. They ban variable indexing, which we prove instead.

**Custom checks to write**

- `cplusp-unscoped-enum`, `-union-decl`, `-bitfield`, `-mutable`
- `-virtual-inheritance`, `-multiple-inheritance` (allow only pure-interface bases)
- `-exceptions` (`throw` and `try`. Verified functions must be `noexcept`)
- `-shared-ptr`, `-iterator-arithmetic`, `-conversion-operator`, `-impure-operator`
- `-function-pointer`, `-coroutine`, `-concurrency` (`<thread>`, `<atomic>`, `<mutex>` use), `-volatile`, `-intrinsics`
- `-unreachable-assume` (`[[assume]]`, `__builtin_unreachable`, `std::unreachable`), `-longjmp`, `-raw-memory-ops` (`memcpy` and friends on non-byte types), `-launder-placement-new`
- `-template-specialization`
- `-markers` (trusted has a contract, reasons non-empty, no verified-to-plain calls)
- `-index` (emits every function's range and kind in the same run, so the driver needs no second parse)

**Delivery**

- [ ] Phase 0 thin slice: one function verified end to end, two chained, one broken each way
- [ ] Plugin skeleton: builds, loads and lists its checks. One custom check with its sample pair
- [ ] Policy YAML schema and the config it emits, with a golden test
- [ ] `-markers` and `-index`. Driver maps edits to functions and filters by kind
- [ ] Remaining custom checks, one sample pair each. Upstream checks compared with their rows, one by one
- [ ] Messages tuned on the bot: what, why, use instead
- [ ] CI job running the same command: fail on violation, SARIF for PR annotations, verified / trusted / plain delta
- [ ] Decide on the approval rule for new trusted and plain markers, and add it if yes
- [ ] Run on 3–5 real hot-path files. Tune decisions from the noise

## Tech stack

Provisional. Parked as "maybe" where the first slice does not need a decision, and stated where it does.

| Piece | Choice | Status |
| --- | --- | --- |
| Gate checks and index | C++20 clang-tidy module. CMake and Ninja. LLVM 18 pinned, builds against 17 to 20 | Forced: a clang-tidy module can only be C++ |
| Driver `cplusp` | Rust. No Python anywhere. TypeScript not in the core | Preferred |
| Prover | Dafny underneath, with the gated C++ translated to it and errors mapped back to C++ lines. The translator is the new trusted component. We test it by compiling the Dafny and running both on the same inputs | Proposed, pending the thin slice |
| Prover, plan B | Verus, via translation to Rust. Exact machine ints and fast, but translated C++ must satisfy the borrow checker | Fallback |
| Prover, dropped | VeriFast directly on C++. Immature frontend, thin LLM familiarity | Not primary |
| Spec syntax in C++ | `//@ requires` / `//@ ensures` comments with Dafny-flavoured expressions, carried through by the translator | Open |
| Check tests | Rust runner over the sample pairs, reading `// CHECK-MESSAGES` lines | Preferred |
| Bot integration | A skill tells the bot to run `cplusp verify` after writing C++ and to act on the messages. No automatic hook | Decided |

## Later phases and open questions

| Phase | Delivers | Exit test |
| --- | --- | --- |
| 0. Thin slice | One command, one function, gate plus proof, messages a bot can act on | The three runs above pass. Prover and spec syntax settled |
| 1. Gate | Every row enforced with a sample pair, policy file, driver, CI backstop | Runs on 3–5 real hot-path files with tolerable noise |
| 2. Trusted base | Contracts for `std::array`, `span`, `vector`, `optional`, `expected`, `unique_ptr`, plus existing-code contracts | Phase 0 functions prove against library contracts, not stubs |
| 3. LLM loop | A skill drives the loop: generate, run `cplusp verify`, fix on the message. A bounded checker is the fallback for counterexamples | The bot gets most new functions to verified without human edits |

**Open questions**

- Does the translator route work for templates and rvalue references? The thin slice decides the Templates and move rows.
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
- Added the principle that verified code has no undefined behaviour, split between gate and prover. Added a Stage column that records which stage guarantees each row.
- Added rows: `memcpy` family and `std::launder` / placement new as Trusted only. `[[assume]]` / `unreachable` and `setjmp` / `longjmp` as Ban.
- Swapped the C-style cast check to `google-readability-casting` after the named check let a narrowing cast through. Noted that the union check fires on access only.
- Made the first step a thin end-to-end slice instead of the gate alone.
- Recorded that the gate runs separately from, and never edits, a team's existing clang-tidy config, with its own pinned clang-tidy.
- Replaced VeriFast as the primary prover with Dafny via translation, provisional on the thin slice. Verus is plan B.
- Added a provisional tech stack: C++ only for the clang-tidy module, Rust for the rest, no Python.
- Rewrote the doc in STE-flavored mode with the asd-ste100 skill: no semicolons, sentences of 25 words or fewer, one word per action.
- Added an Examples section with a verified function, a chained caller, both failure messages, and the marker kinds. It ends with an excerpt of the trusted `vector` contract.
- Named the limit of every Restrict row in its Decision cell.

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
- **Pieces are swappable.** The gate, the driver, the translator and the prover have narrow interfaces. The gate emits findings. The driver emits the verified set. The translator emits prover input. The prover emits pass or fail with locations. You can replace any one without touching the others. The prover is a plug-in behind the interface in Prover interface. We expect to run more than one.
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

## Prover interface

The prover is a plug-in. Any prover works as long as its adapter meets this interface. Decided Oct 3, 2026: design for several, build one first, add a second later as a cross-check.

**What goes in**

1. The functions to prove, each with its C+P body and its contract in our `//@` notation.
2. The contracts of everything those functions call. Verified, trusted and library contracts alike. Never their bodies.
3. The policy, for the rows the prover owns. For example, that float values are opaque.

**What comes back**

For each function, one of:

- `proved`.
- `not proved`, with a list of failures. Each failure has a location in the C++ source, the kind of obligation that failed, and a sentence the gate can print after `Not proved:`. The kinds are fixed: overflow, bounds, division, null or dangling reference, invalidated reference, callee precondition, own postcondition, invariant, termination, unlisted state. A counterexample with input values is optional.
- `timeout`, with the time limit it hit.

Plus the prover's name and version, so a report says which prover said what.

**What an adapter must guarantee**

- **The bot never writes prover-specific hints.** Contracts stay in our notation. Whatever the prover needs beyond them, such as Dafny assertions or VeriFast ownership steps, the adapter supplies or synthesises. If an adapter cannot do that for some construct, the construct's row moves to Restrict or Trusted only. It does not leak into the contract syntax.
- **Same input, same verdict.** Pinned prover version, fixed time limit, no randomness. CI and the bot must see the same answer.
- **Locations map back to C++ lines.** The bot never sees translated code.
- **Two adapters agree.** In cross-check mode the gate runs two provers on the same function and reports `proved` only if both do. Disagreement is reported as a translator bug, not a code bug.

The message layer above the interface does not change when the prover does. `Not proved:` reads the same whichever prover produced it.

## No undefined behaviour in verified code

A verified function has no undefined behaviour, ever. The two stages split the work:

- **UB that lives in the construct** is the gate's job. The code is wrong whatever values flow through it. Or it blinds the prover so that nothing after it can be proved. Examples: reinterpret casts, unions used for punning, pointer arithmetic, C-style casts, `[[assume]]` and `unreachable`, reading a variable that was never initialised. The gate bans these or limits them to trusted code, and catches them instantly.
- **UB that depends on values** is the prover's job. Examples: signed overflow, division by zero, shifting too far, indexing past the end, following a null or dangling reference. This is good-looking code that is only wrong for some inputs. The prover must prove the built-in promise for every verified function.

The Stage column in the table below records which stage guarantees each row.

## State: members, statics and globals

Hidden state is the enemy of a per-function proof. A function that reads a global depends on an input its signature does not show. A function that writes one has an output its signature does not show. So the contract treats state as inputs and outputs, and names it.

Two clauses do this:

- `//@ reads a, b` names the state the function may read beyond its parameters.
- `//@ modifies a` names the state the function may write. Everything not listed is unchanged on exit. The prover relies on that in every caller.

`old(a)` is the value on entry, so `ensures` can describe the change.

The rules, proposed:

1. **Members.** `this` is an implicit parameter. A member function may read and write its own fields without listing them. The contract talks about the fields by name. A class may carry an invariant: every public member function assumes it on entry and re-establishes it on exit. Constructors establish it. Private helpers may break it in between.
2. **Globals, statics, static members, function-local statics.** A verified function must list each one it touches in `reads` or `modifies`. The gate rejects an unlisted access.
3. **Constants.** `const` and `constexpr` globals are values, not state. No listing.
4. **Threads.** Threads are trusted only, so verified code sees state as single-threaded. A trusted caller that runs verified code on several threads owns that risk, and says so in its reason.

A class with an invariant:

```cpp
class Counter {
  int32_t count_ = 0;
  int32_t limit_;
  //@ invariant 0 <= count_ <= limit_
public:
  //@ requires 0 <= limit
  //@ ensures  count_ == 0 && limit_ == limit
  explicit Counter(int32_t limit) : limit_(limit) {}

  //@ modifies count_
  //@ ensures  result ==> count_ == old(count_) + 1
  //@ ensures  !result ==> count_ == old(count_)
  bool tick() {
    if (count_ == limit_) return false;
    ++count_;
    return true;
  }
};
```

The invariant is what lets `tick` prove `++count_` cannot overflow. It also lets every caller know the count is in range without reading the class.

A global as an input and an output:

```cpp
static int64_t g_bytes_sent = 0;

//@ requires 0 <= n
//@ requires g_bytes_sent <= INT64_MAX - n
//@ modifies g_bytes_sent
//@ ensures  g_bytes_sent == old(g_bytes_sent) + n
void account(int64_t n) {
  g_bytes_sent += n;
}
```

After a call to `account(n)`, a caller's proof knows two things. `g_bytes_sent` grew by `n`. Every other global is unchanged, because `account` did not list it. That second fact is what keeps proofs local once state exists.

An unlisted access, and what the bot hears:

```cpp
int64_t sent_so_far() {
  return g_bytes_sent;
}
```

```
Not provable: sent_so_far, line 2: reads g_bytes_sent, which is not in the contract's reads clause. Add `//@ reads g_bytes_sent`.
```

This is the State row of the table. The gate checks the listing. The prover checks the claims.

### Variables other threads may change

A per-function proof assumes that nothing changes under it. A variable another thread can write breaks that assumption twice. A plain read of it is a data race, which is UB. And two reads of it may return different values, so "nothing else changed" is false.

The rule, proposed: **shared state enters verified code only as a value.** Either a parameter, or the result of a trusted getter. Never a direct read or write.

```cpp
// Shared with other threads. Lives behind trusted functions.
static std::atomic<int32_t> g_level{0};

CPLUSP_TRUSTED("atomic load. Every writer keeps 0 <= level <= 100")
//@ ensures 0 <= result <= 100
int32_t current_level();

CPLUSP_TRUSTED("atomic store")
//@ requires 0 <= level <= 100
void set_level(int32_t level);
```

Verified code calls the getter and uses the bound:

```cpp
//@ ensures 0 <= result <= 200
int32_t doubled_level() {
  return 2 * current_level();
}
```

What the getter's contract may say:

1. **Only what is true of every value ever stored.** A range, a non-null promise, a format. That is a promise every writer keeps, in trusted or plain code. The getter's reason names it.
2. **Nothing that relates two calls.** Each call may return a different value. The prover treats the getter as a fresh input every time, like reading a clock.
3. **Nothing inside another contract.** `ensures result == current_level()` is not allowed, because the getter is not a pure function of anything the prover can see.

The trap this prevents:

```cpp
bool stable() {
  return current_level() == current_level();
}
```

```
Not proved: stable, line 2: cannot show the two results of current_level() are equal. Each call may return a different value.
```

Two limits to know:

- **Lost updates are not caught.** `set_level(current_level() + 1)` has no UB and keeps the invariant, so it passes. Another thread can still write between the two calls. For a read-then-write pair, use a trusted function such as a `fetch_add` wrapper with its own contract.
- **Mutex-protected plain variables follow the same rule.** Mutexes are trusted only, so the lock and the data it protects live in trusted functions. Verified code sees only the getters and setters.

Prefer parameters when you can. A trusted caller reads the shared value once and passes it in. The verified function then has one value, its proof is simpler, and the "two reads differ" question never comes up.

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

Generated by `cplusp policy doc` from `policy/cplusp-policy.yaml`. Do not edit by hand.

| Area | Construct | Canonical stance | Why, for us | Decision | Stage |
| --- | --- | --- | --- | --- | --- |
| Types | Fixed-width ints, `bool`, `enum class` | MISRA prefers sized types and scoped enums | Easy for the prover. | Allow | — |
| Types | Plain `int`, `long`, `short`, `char` and the other built-in integer types | MISRA Dir 4.6: use typedefs that show size and signedness | The compiler sets the width and the signedness of these types. The source does not say them, and the proof needs them. | Ban | Gate |
| Types | Unscoped `enum` | MISRA: use scoped | Implicit int conversion. | Ban | Gate |
| Types | `double` | Allowed by all | The model is a real after one rounding per operation, with the error bound of IEEE 754 binary64 as an axiom. It has no NaN and no infinity, so the contract must keep them out. | Restrict: Finite values only, stated in the contract. A contract gives an error bound, never an equality. One operation per expression. | Prover |
| Types | `float` and `long double` | Allowed by all. Our model is of one type | The model is of IEEE 754 binary64. A float or a long double would prove against bounds that are not its own. | Trusted only | Gate |
| Types | Unions | Banned by MISRA and Core Guidelines | Type punning breaks the memory model. | Ban | Gate |
| Types | Bit-fields | MISRA advisory ban | Layout is implementation-defined. | Trusted only | Gate |
| Types | Uninitialised variables | MISRA and Core Guidelines ban | Reading them is UB. | Ban | Gate |
| Arithmetic | Signed/unsigned arithmetic, shifts, division | Allowed with care | The prover proves no overflow, bad shift or divide by zero. | Allow | Prover |
| Arithmetic | Comparison of a signed with an unsigned integer | MISRA 10.4, -Wsign-compare | The signed operand converts to unsigned, so a negative value compares as a large one. | Ban | Gate |
| Arithmetic | Implicit narrowing conversion | Core Guidelines ES.46 | The value changes with no sign in the source. C++20 wraps an integer, and a double loses its fraction. | Ban | Gate |
| Arithmetic | Implicit conversion of a signed integer to unsigned | MISRA 10.3, -Wsign-conversion | A negative value becomes a large one with no sign in the source. | Ban | Gate |
| Arithmetic | Multiplication in a narrow type whose result widens | Core Guidelines ES.103 | The product overflows in the narrow type before it reaches the wide one. | Ban | Gate |
| Arithmetic | Shift of a literal of type int | MISRA 12.2 | The literal is an int, so the shift is 32 bits wide whatever the destination type. | Ban | Gate |
| Arithmetic | `==` or `!=` on `double` values | MISRA 2023 and Core Guidelines warn, -Wfloat-equal | Two computations of one value differ in the last bit, so equality is not a fact the model can state. | Ban | Gate |
| Arithmetic | A floating-point literal that is not exactly a double | No stance. The model reads a literal as the real it spells | The compiler rounds the literal to the nearest double before any operation. The model reads the real it spells, so the contract counts one rounding too few. | Ban | Gate |
| Arithmetic | A call that changes the floating-point rounding mode or control register | MISRA 2023 bans <cfenv> writes | The double model assumes round to nearest even for every operation in the process. | Ban | Gate |
| Arithmetic | Two `double` operations in one expression | -ffp-contract, MISRA advisory | The compiler may fuse two operations into one rounding, and the model rounds once per operation. | Restrict: One `double` operation per expression. A comparison compares values, not results of arithmetic. | Gate |
| Arithmetic | Narrowing `static_cast` | Allowed if explicit | The prover proves the value fits. | Allow | Prover |
| Memory | Non-owning raw pointer to one object | Core Guidelines allow as observer | Nullability goes in the contract. A stored pointer can outlive its object, and the model has no object that dies. | Restrict: A parameter only. One object, no ownership, no arithmetic. No pointer member, no pointer local, and no pointer as a template argument. | Gate |
| Memory | Pointer arithmetic, array-to-pointer decay | Core Guidelines bounds profile ban | Pointer arithmetic has no bounds the prover can see. | Ban | Gate |
| Memory | `new` / `delete`, `malloc` / `free` | MISRA advisory ban | Allocation is trusted. Ownership goes through RAII types. | Trusted only | Gate |
| Memory | `memcpy`, `memset`, `memmove` on anything but plain bytes | Core Guidelines discourage | Bypasses the type model. UB on non-trivial types. | Trusted only | Gate |
| Memory | `std::launder`, placement `new` | Rare in application code | Object-lifetime games the prover cannot follow. | Trusted only | Gate |
| Memory | `std::unique_ptr` | Recommended | Simple single ownership, behind a trusted contract. A const reference is a value in, decisions 0029 and 0033, so what it owns may not change through it. | Restrict: Const access only through a const handle or a const container of handles. No write through one. No assignment, increment or non-const call on what it owns, and no binding of that to a non-const reference, pointer or span. | Gate |
| Memory | `std::shared_ptr` | Allowed | Shared ownership and refcounts are hard to reason about. | Trusted only | Gate |
| Memory | Lvalue references | Allowed | The model has no heap, decision 0029. A reference member or local is a second name for an object, and a value model cannot see it. | Restrict: A parameter only. No reference member and no reference local, and none in disguise. A disguise is a `std::reference_wrapper`, a tuple or pair of references, or the reference of a `std::vector<bool>` or a `std::bitset`. To copy the value, write its type. In a call, two reference arguments never name one object, row `aliasing`. | Gate |
| Memory | Two names for one object in one call | No C++ guideline. Rust's rule: one writer or many readers | The model has no heap, decision 0033, and a value model cannot see two names for one object. When one argument of a call can write, every reference, pointer or span argument and the object of the call must reach a different object. A global bound to a non-const reference, a pointer or a span is State as well, so it has two names too. A const reference to a global is fine in a call into std, which has no State, and a constant is never State. | Ban | Gate |
| Memory | Rvalue refs and `std::move` | Allowed | Prover support to check in the first slice. | Restrict: Move locals and parameters only, no use after move. | Gate |
| Memory | Returning a reference or pointer to a local | MISRA mandatory ban | Always a bug. | Ban | Gate |
| Library | `std::array`, `std::span` | Recommended | Core trusted types. | Restrict: A span as a parameter only, never stored in a local or a member. | Gate |
| Library | `std::string`, `std::string_view` | Allowed by all | Text is a sequence of `char`, whose signedness the compiler sets, and the model has no text type. Verified code reads text as bytes. | Trusted only | Gate |
| Library | `std::cout`, `std::cerr`, streams | Allowed by all | A stream is a global the whole program shares, and output is a side effect no contract describes. The model has no I/O. | Trusted only | Gate |
| Library | `std::vector`, `std::string`, maps | Allowed | Trusted contracts carry the invalidation rules. A reference into a container dies at the next mutation, and the model has only values. | Restrict: Only methods that have a trusted contract. No reference into a container. No iterator held across a mutation. No non-const reference to a container as a local, because a parameter is the only alias. No operator[] on a map. No pointer into a container, by address-of, data(), c_str(), std::data, std::to_address or std::addressof. | Gate |
| Library | `operator[]` with a variable index | Core Guidelines bounds profile ban | The prover proves the index is in range. | Allow | Prover |
| Library | Fold with an init value narrower than the elements | Core Guidelines ES.102 | The fold runs in the type of the init value, so a sum of int64_t values in an int wraps. | Ban | Gate |
| Library | Iterators | Allowed | Iterator arithmetic is pointer arithmetic in disguise. | Restrict: Range-for only. The loop body does not change the range, by a call on it or through a function. begin and end may appear only as direct arguments of a std:: call. No stored iterator, no std::next, prev, advance or distance. | Gate |
| Library | `std::optional`, `std::expected`, `std::variant` | Recommended | Trusted contracts. Replaces unions and exceptions. | Allow | Spec |
| Library | `<algorithm>` with lambdas | Allowed | Each algorithm needs a trusted contract. | Restrict: Only algorithms on the trusted list, which is short at first. | Spec |
| Casts | C-style casts | Banned by MISRA and Core Guidelines | Hides what kind of cast it is. All forms, including plain numeric narrowing. | Ban | Gate |
| Casts | A conversion of a number to an enum class that has no values written | No stance. The model reads each value of the enum as an enumerator | A number that is no enumerator makes a value that the model of the enum does not have. The prover then trusts a switch that the program does not follow. A verified caller trusts each value, so the row holds in trusted code too. | Ban | Gate |
| Casts | A cast that changes the type that a pointer or a reference points to | Undefined behavior, [basic.lval] paragraph 11 and [expr.ref] paragraph 10 | A read of an object through a type that C++ does not list for it has no meaning. The prover sees the type of the object, and the program reads another one. The row holds in trusted code too, because a verified caller trusts the values that a trusted function reads. The row also bans a raw copy of bytes that can make a bad value. A raw copy is a bit cast, memcpy, memmove, memset or a write through bytes. A cast to char, unsigned char or the std::byte of the library is allowed. So is a cast to void*, and a cast that only adds const or volatile. | Ban | Gate |
| Casts | `reinterpret_cast`, `const_cast` | Banned | Defeats the type model. Most forms are UB. | Trusted only | Gate |
| Casts | Downcasts (`static_cast`, `dynamic_cast`) | Core Guidelines ban `static_cast` downcasts | A downcast asserts a type the prover cannot see. Every dynamic_cast counts, including a cross-cast. | Ban | Gate |
| Classes | Classes, constructors, destructors, RAII | Allowed | Core of the subset. | Allow | Prover |
| Classes | Single inheritance, `virtual`, `override`, `final` | eCv++ requires `override`, encourages `final` | The prover checks overrides for Liskov substitution. | Allow | Prover |
| Classes | Mem-initializers out of declaration order | Core Guidelines C.47, -Wreorder | C++ initializes the members in declaration order, whatever order the constructor writes. A member read before its turn is undefined. | Ban | Gate |
| Classes | Copy of a derived object into a base type | Core Guidelines ES.63 and C.145 | The copy keeps the base part only, and a virtual call on it goes to the base. | Ban | Gate |
| Classes | Virtual call in a constructor or destructor | Core Guidelines C.82 | The call goes to the class under construction, not to the derived class. | Ban | Gate |
| Classes | Class with a virtual function and no virtual destructor | Core Guidelines C.35 | Deleting a derived object through a base pointer is undefined without one. | Ban | Gate |
| Classes | Overriding without `override` | eCv++ requires `override` | An override the reader cannot see is a hidden contract change. | Ban | Gate |
| Classes | Multiple inheritance | eCv++: interfaces only | Keep the object model simple. | Restrict: At most one base with data or non-pure functions. Every other base is a pure interface, with only pure virtual functions and a virtual destructor. | Gate |
| Classes | Virtual inheritance | MISRA advisory ban | Not provable today. | Ban | Gate |
| Classes | Operator overloading | eCv++: const, no side effects | Hidden side effects confuse contracts. | Restrict: A const member, or a free function with const or by-value parameters. No assignment, compound assignment, increment or decrement operator unless it is `= default` or `= delete`. | Gate |
| Classes | Implicit conversions (non-`explicit` ctors, conversion operators) | eCv++ requires `explicit` | Hidden calls confuse contracts. | Ban | Gate |
| Classes | `mutable` members | eCv++ ban | Breaks const reasoning. | Ban | Gate |
| Templates | Function and class templates | eCv++: type params only, no specialisation | Verified per instantiation. | Restrict: Type parameters only, no specialisation. | Gate |
| Templates | `constexpr`, `consteval`, concepts | Allowed | Compile-time only. | Allow | — |
| Templates | SFINAE, template metaprogramming | Discouraged | Nothing to prove at runtime, but unreadable contracts. | Trusted only | Gate |
| Control | `if`, `switch`, `for`, `while`, early `return` | Allowed by all | The prover follows them. | Allow | Prover |
| Control | Fall-through between switch cases | MISRA 16.3, -Wimplicit-fallthrough | Control runs into the next case with no sign in the source, and a match in the model has no fall-through. | Ban | Gate |
| Control | Switch that does not cover every value | MISRA 16.4 and 16.5 | A value with no case runs past the switch in silence, and the match in the model must cover every value. | Ban | Gate |
| Control | Exceptions | eCv++ ban. Common in safety code | Verified code is noexcept. | Ban | Gate |
| Control | `goto` | MISRA ban | No benefit. | Ban | Gate |
| Control | `[[assume]]`, `__builtin_unreachable`, `std::unreachable` | New in C++23 | UB if the claim is false. Claims belong in the contract, where the prover checks them. The C++23 `[[assume]]` attribute is not caught yet. | Ban | Gate |
| Control | `setjmp` / `longjmp` | MISRA ban | Skips destructors. UB in C++. | Ban | Gate |
| Control | Recursion | MISRA ban | The prover needs a termination measure. Loops are easier. | Restrict: Needs a `decreases` clause in the contract. | Prover |
| Control | Two changes of state in one expression | MISRA 13.2. Core Guidelines ES.43 and ES.44 | C++ does not fix the order of two calls in one expression, and compilers differ. Two increments of one variable in one expression are undefined. | Restrict: Two changes of state in one full expression only where the standard orders them. Function arguments and the operands of an arithmetic or comparison operator are not ordered. Beside an unordered change of state, an operand is a literal, or a local or parameter the change does not write. Not a call, not a global, and not a member of an object the change writes. A call may change state when a parameter is a non-const reference or pointer, or when it is a non-const member function. A call into `std` counts too. The casts `std::move`, `std::forward` and `std::as_const`, the accessors `begin`, `end`, `at`, `front`, `back` and `get`, and the makers `make_pair`, `make_tuple` and `tie` change nothing through their parameters. What their code runs counts, as a copy of an argument does. A default member initializer and the capture initializer of a lambda run where the expression is written. | Gate |
| Control | Lambdas | Allowed | Captured references can dangle. | Restrict: Passed directly to a std:: call, capturing by value only. No capture by reference, no capture of this, and not mutable. | Gate |
| Control | Function pointers, `std::function` | eCv++ allows with contracts | Indirect calls need contracts on the target. | Trusted only | Gate |
| Control | Varargs, coroutines | Banned by Core Guidelines (varargs) | Not provable. | Ban | Gate |
| Concurrency | Threads, atomics, mutexes | Allowed in MISRA | Concurrent proofs are far harder. Isolate them. | Trusted only | Gate |
| Concurrency | Variables other threads may change | Allowed in MISRA with care | Each read may see a different value. See State in the plan. | Restrict: Through a parameter or a trusted getter, never a direct read or write. | Spec |
| Concurrency | `volatile` | MISRA restricts | Hardware access only. A volatile qualifier on a member function is not caught yet. | Trusted only | Gate |
| State | Global with a dynamic initializer | Core Guidelines I.22, -Wglobal-constructors | Globals in different files initialize in an order the standard leaves open, so one may read another before it exists. | Ban | Gate |
| State | Globals, statics, static members, function-local statics | MISRA restricts globals | Hidden state breaks modular proofs. A global is a field of the State value the function takes in and gives back, decisions 0011 and 0035. The model needs the list to know which functions take it. | Restrict: On the contract's `//@ modifies` line when the body changes it. On `//@ reads` or `//@ modifies` when the body reads it, directly or through a call. A call brings what its callee lists, or what the compiler generates for it. An override lists no more than the function it overrides. Constants exempt. Members are implicit. | Gate |
| State | A function-local static variable | MISRA restricts statics | Its state has no name a caller's contract can list, so no caller can prove anything about a call that changes it. | Ban | Gate |
| Platform | Inline asm, SIMD intrinsics | MISRA restricts asm | Hot-path code goes behind a contract. | Trusted only | Gate |
| Platform | Function-like macros | MISRA advisory ban | Hides code from the prover. The markers of include/cplusp.h are the one exception, because they carry no code. | Ban | Gate |
| Platform | Compiler builtins | Not in any guideline | A `__builtin_` call is the compiler's own function, with no contract and often undefined behaviour on the wrong argument. The three that mark unreachable code have their own row. | Ban | Gate |
| Platform | A construct no row names | Decision 0032. An allowlist, not a blocklist | The gate refuses what it does not know. Every kind of statement, expression, declaration and type that verified code may use is on the lists in this row. So is every attribute. A kind outside them has no rule yet, so no proof covers it. The kinds a ban row claims are listed here too, under the row's name. So a team that loosens the row loosens its kinds with it. | Ban | Gate |

## Markers and the escape hatch

Three markers, and one that waits. They are the only way a function changes kind. The gate reads them, decision 0039.

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

- `CPLUSP_VERIFIED` promotes an existing function into the verified set. New functions need no marker. They are verified by default. A lambda, a local class and an explicit specialization take only the markers written on them, decision 0047. In a plain body they are plain, decision 0048.
- `CPLUSP_TRUSTED(why)` keeps a contract and skips the proof. The gate does not check its body against the Trusted only rows. The gate still enforces its contract on every caller.
- `CPLUSP_PLAIN(why)` opts a new function out entirely. Verified code cannot call it. A class takes it too, decision 0051. Verified code then makes no object of the class, reads none of its fields, and hands it to no library call, decisions 0052 to 0054. It reaches the class through a trusted member.
- `CPLUSP_ASSUME(why)` covers a single statement, such as one `reinterpret_cast` in an otherwise provable function. It waits until a case needs it.

`clang::annotate` survives into the AST, so the gate and the prover both see it. We checked this on clang 18, including the reason string. GCC builds compile it away.

Rules the gate enforces:

1. **A trusted function has a contract.** Without one, the gate cannot check callers against it. Message: "Not provable: {file}:{line}: marker: fast_sum is trusted and has no contract. Its callers rest on the contract alone."
2. **Every marker carries a reason.** Trusted, plain and assume markers must carry a non-empty string.
3. **The gate reports exceptions.** Each run prints the verified, trusted and plain counts for the change, with reasons, and the change from the base branch. The counts wait for the CI report, decision 0039. Whether a human must approve new trusted or plain markers before merge is open. The loop never blocks the bot on it.
4. **Verified code calls only contracted code.** A call from a verified function to a plain one fails the gate. The gate reads the calls that run from the lowered form, decision 0047. A destructor, a call from the library and a virtual call count too. An indirect call that the gate cannot name is a finding of `function_pointers`, decision 0048. The message names the callee: "Not provable: {file}:{line}: marker: verified code calls legacy_parse, which is plain. Give it a contract and mark it trusted."

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

There is no translator, decision 0017, and the prover is Dafny with a hand-written model. The first match check is the differential run, decision 0034: the model and the C++ run on the same inputs and must print the same. Exit test: all three steps run from one command, with messages a bot can act on without reading anything else. This settles the spec syntax and the shape of the messages before we build any more breadth.

## Phase 1: the gate

The gate has two parts. A clang-tidy module rejects any verified function that uses a banned construct. A driver computes the verified set and shapes the messages. About half the rules reuse existing checks. The rest are short AST-matcher checks.

**Design choices**

- **A separate run, alongside existing team configs.** The gate invokes clang-tidy with its own generated config, its own loaded plugin, and the team's `compile_commands.json`. The gate never reads or edits the team's `.clang-tidy`. Their normal lint run does not change. The gate fails only on policy rows, so team settings cannot add noise or silently disable our checks.
- **Versions decoupled.** The gate brings its own pinned clang-tidy. Teams on clang-tidy 16 through 20 see no change. The plugin also builds from source against LLVM 17 to 20, for teams that want it in their editor. A team's own loaded plugins coexist with ours.
- **Function granularity.** The unit is a function, never a file. The driver maps uncommitted edits to enclosing functions and applies the membership default. It adds callers of any function whose contract changed.
- **An allowlist first, then one generic check driven by the policy.** The gate refuses every node kind the policy does not list, decision 0032. A ban row that is a whole kind names its kinds and needs no pattern. For a shape inside an allowed kind, the check `cplusp-matcher` compiles clang AST matcher patterns from its options, as `clang-query` does, decision 0016. Only the rows that need real code have a hand-written check. They are these: `mutable`, lambda limits, impure operators, multiple inheritance, iterator arithmetic and evaluation order. Also inexact literals, aliasing, const handles, unlisted state, raw copies of bytes, line directives, pragmas, and the function index with its markers.
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
| Recursion | the prover | `misc-no-recursion` flags every recursive call. The row only bans recursion without a `decreases` clause, and Dafny demands one |
| Use after move | `bugprone-use-after-move` | The gate half of the rvalue row |
| Returning a reference to a local | `clang-diagnostic-return-stack-address` | A compiler warning, enabled through clang-tidy |
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
- [ ] The differential run, decision 0034: six cases with drivers, the naive model caught on each
- [x] Plugin: builds, loads, lists its checks. One generic check driven by policy patterns, 29 sample pairs
- [x] Policy YAML schema and the config it emits, with a golden test
- [x] `-markers`, decision 0039. The driver gives each finding the kind of the function that holds it, and the core decides whether it stands
- [ ] `-index`. The driver maps edits to functions
- [x] Hand-written checks that read no contract: `-mutable`, `-multiple-inheritance`, `-impure-operator`, `-iterator-arithmetic`, `-lambda-limits`, `-evaluation-order`, `-inexact-literal`, one sample pair each
- [x] `-aliasing` and `-const-handle`, decision 0033, and the read rule in `-evaluation-order`
- [x] `-allowlist`, decision 0032. Six ban rows name their kinds instead of a matcher, and the lists are seeded from the corpus and reviewed
- [x] `-unlisted-state`, decision 0035. The gate reads the `modifies` and `reads` lines, the one piece of contract it reads. It judges the code the compiler generates, decision 0037
- [ ] Hand-written checks that read contracts, after docs/soundness.md settles the contract language: `-index`. `-markers` reads only whether a contract is there. Recursion and unlisted state are the prover's, decision 0025
- [x] Messages: what, why, use instead, in the shapes docs/policy.md fixes. Tuning on a real bot still to do
- [ ] CI job running the same command: fail on violation, SARIF for PR annotations, verified / trusted / plain delta
- [ ] Decide on the approval rule for new trusted and plain markers, and add it if yes
- [ ] Run on 3–5 real hot-path files. Tune decisions from the noise

## Tech stack

Provisional. Parked as "maybe" where the first slice does not need a decision, and stated where it does.

| Piece | Choice | Status |
| --- | --- | --- |
| Gate checks and index | C++20 clang-tidy module. CMake and Ninja. LLVM 18 pinned, builds against 17 to 20. The gate also runs `clang++-18 -MM` for the compiler's list of the files a build includes, decision 0038 | Forced: a clang-tidy module can only be C++ |
| Driver `cplusp` | Rust written in Verus from day one, one static binary. No Python anywhere. TypeScript not in the core. See Proofs about cplusp itself | Decided |
| Translator | Decisions 0056 and 0057. The clang-tidy check `cplusp-tree` writes each function as JSON in the core's shape, a trusted edge. The shell's `crates/cplusp/src/model.rs` reads it. The core cuts the `//@` lines into tokens and folds the named constants and enumerators, `crates/cplusp-core/src/contract.rs` and `fold.rs`, decision 0124. The shell prints the Dafny text, with the prelude and each sequence as `Vec<T>`, a trusted edge. The prelude function `CountIf` is the model of `std::count_if` with a lambda, decision 0149. Dafny proves its body, so it adds no axiom. When a name of the double model is printed, the model also holds the module `Double` from `divergence/dafny/Double.dfy`, decision 0154. Its axioms `RoundError` and `RoundExactInt` are axioms that the translator brings, and `prove` names each on an `Axiom:` line when the model uses it. The contract of `StdSort` in `divergence/dafny/Algorithm.dfy` is another, decision 0161. An interface brings one axiom, the contract of each of its pure virtual functions. The shell prints the lemma that checks each override against it, decision 0165. The upcast of each class over the interface says that a call through the interface gives the value of the override, decision 0166. `prove` names each interface on an `Axiom: model:` line. The Verus core `crates/cplusp-core/src/model.rs` parses the contracts and makes each rule of the translation, with proofs. `cplusp prove` runs the gate, the translator and Dafny. The shell `crates/cplusp/src/prove.rs` runs Dafny and prints the sentences, a trusted edge, decisions 0068 and 0069. The core reads the output of Dafny and gives the verdict, `crates/cplusp-core/src/dafny.rs`, decisions 0077 and 0127. The Verus core `crates/cplusp-core/src/companion.rs` scans the companion file of specification functions, decisions 0080, 0083 and 0123. It proves that a file passes only when no byte, comment or token breaks the rules. The spec of the lexer is the definition of how Dafny reads the bytes. The tests in `crates/cplusp-core/tests/companion.rs` are its evidence. The shell reads the file and makes the sentences. The reader trusts the summary of Dafny and its `PATH(L,C): Error:` lines. It also trusts the map from each line of the model to its C++ place. The translator does not yet carry each row of the policy. For example, it models a C-style cast between integers as a cast, and the gate's check still bans it | Decided, fifth slice built: `radix_find` proves end to end |
| Policy to clang-tidy conversion | A pure core inside the driver: policy in, config out, findings matched back to rules, filter by function kind. Proved in Verus: every check of every non-allow rule is enabled, and nothing else | Decided |
| Prover, candidate A | Dafny underneath, with the gated C++ translated to it and errors mapped back to C++ lines. Strong automation and the most LLM training data of any verifier. The translator is the new trusted component. We test it by compiling the Dafny and running both on the same inputs | Open. The thin slice decides which is built first |
| Prover, candidate B | VeriFast. Native `//@` contract syntax, built-in overflow and bounds checks, and ownership gives frame and invalidation rules for free. Costs: its C++ frontend lacked templates in 2022. Release notes to Sept 2026 show the work going to Rust. So we would translate to its mature C mode. A 2026 study of ten LLMs found 31% verification success on VeriFast specs, with 94% of errors in separation-logic details | Open. The thin slice decides which is built first |
| Prover, plan C | Verus, via translation to Rust. Exact machine ints and fast, but translated C++ must satisfy the borrow checker | Fallback |
| Spec syntax in C++ | `//@ requires` / `//@ ensures` comments with Dafny-flavoured expressions, carried through by the translator | Open |
| Check tests | Rust runner over the sample pairs, reading `// CHECK-MESSAGES` lines | Preferred |
| Bot integration | A skill tells the bot to run `cplusp verify` after writing C++ and to act on the messages. No automatic hook | Decided |
| Ply | Not a dependency. Verus proves the source itself. Ply becomes interesting later for fuzzing the untrusted edges and for drawing the proved-versus-not picture of cplusp | Decided Oct 3, 2026 |

## Proofs about cplusp itself

Decided Oct 3, 2026: we prove as much of our own tooling as the tools allow. Fewer bugs in the gate means fewer silent holes in the subset.

**We write the driver in Verus from day one.** Verus proves Rust code directly. The proved code is ordinary Rust after the annotations are stripped. Writing in Verus at the outset shapes the code so it can be proved. Retrofitting proofs onto plain Rust is harder. The specifications are light at first and deepen as each format settles.

**What we prove**

- **Policy to config.** Every check of every rule whose decision is not `allow` is enabled, with its options. No other check is enabled. A team override changes only the entries it names. A loosened entry always carries its reason.
- **Finding to rule.** Every finding from an enabled check maps to exactly one rule. A finding inside a trusted function is dropped only if its rule is Trusted only.
- **The verified set.** Every edited function is classified, each into exactly one kind. Callers of a function whose contract changed are included. No function is counted twice.
- **The translator's shape.** Every function handed to the prover comes back with a verdict. Every contract line in the C++ appears in the prover input. Every location in a verdict maps back to a C++ line.
- **The flags of the compiler.** A run with no refusal sets `-std` at C++23 or later, decision 0128. Its last contraction flag sets contraction off. No flag changes floating point, changes what the compiler reads or reports, or hides a warning of the policy.
- **The verdict of `prove`.** `Proved` needs three facts in the output of Dafny, decision 0127. A clean summary line counts each method. No line is an error line. No line is an axiom on the companion file.
- **The contract lexer.** The lexer of a contract line drops no text except ASCII white space, decision 0124. A number is the value of its digits in its base. A name becomes a constant or an enumerator only by the rules of 0106 and 0109.
- **The companion file.** A companion file passes only when four things are true, decision 0123. It holds no refused byte. Each comment ends. No token is a refused keyword, `"`, `@` or `{:`. No declared name is a name of the model. The proof holds under the spec of the lexer, and tests are its evidence.

**What we cannot prove, and what we do instead**

- **Meaning.** That the translated code means the same as the C++ needs a formal semantics of both languages. Out of reach. Instead: differential tests that compile the prover's version and run both on the same inputs, and the two-prover cross-check from Prover interface.
- **The edges.** Reading files, running clang-tidy and git, parsing YAML, writing the report. Verus treats these as trusted functions with contracts, the same way cplusp treats `memcpy`. We keep them thin and list them. Every build prints the size of this trusted surface, exactly as the gate prints it for user code.
- **The clang-tidy module.** C++ has no prover we would use on it. The module stays small, mechanical, and covered by the sample pair of every rule.
- **The trusted contract library.** Contracts for `vector`, `span` and the rest are axioms. Review and tests, not proofs.

**Where this costs us.** Verus does not support all of Rust. No trait objects in proved code, limited closures, weak reasoning about string contents. So the proved core works on structured data. The final step that turns a structure into YAML text is one of the thin trusted edges. Verus also tracks a pinned Rust nightly, so the toolchain is pinned with it.

## Later phases and open questions

| Phase | Delivers | Exit test |
| --- | --- | --- |
| 0. Thin slice | One command, one function, gate plus proof, messages a bot can act on | The three runs above pass. Prover and spec syntax settled |
| 1. Gate | Every row enforced with a sample pair, policy file, driver, CI backstop | Runs on 3–5 real hot-path files with tolerable noise |
| 2. Trusted base | Contracts for `std::array`, `span`, `vector`, `optional`, `expected`, `unique_ptr`, plus existing-code contracts | Phase 0 functions prove against library contracts, not stubs |
| 3. LLM loop | A skill drives the loop: generate, run `cplusp verify`, fix on the message. A bounded checker is the fallback for counterexamples | The bot gets most new functions to verified without human edits |

**Open questions**

- Dafny or VeriFast underneath? The thin slice runs the same function through both by hand before any translator is built.
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
- Made the prover an open choice between Dafny and VeriFast, settled by the thin slice. Verus is plan C.
- Added the Prover interface: the prover is a plug-in, the bot never writes prover-specific hints, and two provers can run as a cross-check.
- Decided the driver is Rust written in Verus from day one. Added Proofs about cplusp itself: what we prove, what we cannot, and what we do instead.
- Built the verified core (29 behaviour tests, 44 Verus proofs), the command (28 tests) and the clang-tidy plugin with its one generic check. Eighteen rules detect through matcher patterns in the policy file. 29 sample pairs. The subset table below is generated from the policy file. Decided against ply as a dependency. Changed the message grammar so the construct name is followed by a colon.
- Added `cplusp policy show` and the generated subset table, see policy.md.
- Added a provisional tech stack: C++ only for the clang-tidy module, Rust for the rest, no Python.
- Rewrote the doc in STE-flavored mode with the asd-ste100 skill: no semicolons, sentences of 25 words or fewer, one word per action.
- Added an Examples section with a verified function, a chained caller, both failure messages, and the marker kinds. It ends with an excerpt of the trusted `vector` contract.
- Named the limit of every Restrict row in its Decision cell.
- Added the State section: members are implicit, globals and statics are listed in `reads` or `modifies`, constants are exempt. Added the `-unlisted-state` check.
- Added the rule for variables other threads may change. They enter verified code only as values, through a parameter or a trusted getter. The getter's contract is a per-value invariant.
- Built the divergence battery for Dafny, decisions 0017 to 0020. It has 62 cases. Each has the C++ as the bot writes it, two models, a witness under the sanitizers, and its rule in the skill. The battery found 17 gate rows. Among them: plain `int`, implicit narrowing, sign conversion, two state changes in one expression, slicing, and `==` on floats. Floats stay in the subset as a real after rounding. The baseline is C++23, decision 0022. The gate refuses fast math, a lower standard, a missing `-ffp-contract=off` and a silenced warning, decision 0021. The subset table below is regenerated.
- Verified code is `double` only, decision 0024. The row `double_only` refuses `float` and `long double`, and the model file is `Double.dfy`. The battery has 68 cases. The cases and the rows about `double` say `double`, not float.
- An outside review found nine holes in the gate. Decision 0025: the gate refuses a run it cannot enforce, and judges the flags of a compile database. A diagnostic pragma in a file or its headers is a finding.
- The review's pattern holes are closed and kept as banned lines. They are parentheses and a member around a range, a container alias, `auto` and a literal around a float or an int. Also a bare `new` and `std::atomic_ref`. The evaluation-order row is a check that follows the standard's sequencing, decision 0026.
- A floating-point literal that is not exactly a double is refused, decision 0027. The battery case `double_literal` found it: `a * 0.1` rounds twice where the contract counts once. The battery has 69 cases.
- A second review found fifteen more holes. Among them: a `#line` directive that hides a pragma, and a flag that strips the preprocessor's line markers. Also five ways a call changes state that the sequencing check did not count. Each is a banned line or a fixture now.
- Added `examples/`: one folder per row the bot may use, with the C++ under the row and the Dafny for it. A test runs the gate on each C++ file and Dafny on each model. A `trusted_only` row also shows the trusted body, which the gate refuses under that row.
- Decision 0028: a member function's contract uses the implicit `this`. Members are never listed in `modifies` or `reads`, and the class invariant is a predicate method every public method names. No class-level clause, in any prover.
- Decision 0029: the model has no heap. An object is a datatype, and a method takes it in and gives it back. A pointer is an `Option`, and an interface is an opaque type with its contract. A reference is a parameter only, under the row `lvalue_references`, and two non-const references carry `requires &a != &b`. The test `the_model_has_no_heap` refuses a heap construct in any example or mitigated model.
- Fourteen design patterns under `examples/`, each in the shape the subset takes, with the gate's refusal of the classic form quoted. Decision 0030 closes what the round found. Const reaches through a `unique_ptr`, and a function-local static is refused. A downcast inside a template and a pointer as a template argument are refused too. `std::expected` does not compile under the pinned toolchain, which the soundness map records.
- Seventeen hot-path idioms and day-one questions under `examples/`. Decision 0031: text is bytes in verified code, `std::string` is trusted only, a search returns an optional, and a larger example may carry a trusted body. The two rows whose check was never built are the prover's.
- A third review found four holes, all in the new value model's claim that it is exact. Decision 0033: one root, one writer. In a call where one argument can write, no two reference, pointer or span arguments reach one object. No contract carries a clause about addresses. Const reaches through a handle for every spelling of a write. Beside an unordered change of state only a literal or an untouched local may stand. A line marker written in the source is a finding. Decision 0032: the gate becomes an allowlist of node kinds. 76 rules, 62 enforced by the gate.
- Decision 0034: the differential run. A case may carry a driver pair, and the command compiles the model and the C++ and runs both on generated inputs. Six cases carry one. The naive model must diverge wherever the case says it is wrong.
- Decision 0032 built: the gate is an allowlist. The row `unlisted` lists 56 statement kinds, 22 declaration kinds and 16 type kinds, seeded from 210 gate-passing files and reviewed by hand. A kind outside the lists is refused with its name. Decision 0035 built: the gate reads the `modifies` and `reads` lines and refuses an access to a global they do not list, also through a call. The row `iostreams` came from the first trial run on a real file, where most findings were lines printing to std::cout. 78 rules, 65 enforced by the gate.
- A fourth outside review and a second inside review found eleven ways past decisions 0032 to 0035. All had one shape: an analysis that did not finish, counted as a pass. Decision 0036: an analysis that cannot finish refuses. Templates are judged at their instantiations, and an unread callee changes state. No depth limit ends in a pass, and the compiler's own lexer reads the source for directives.
- A third inside review found fourteen more ways past the state check and the directive scanner. Eleven were code the compiler runs for the author, which the check had to find for itself. Decision 0037: the gate reads the compiler's lowered form. The state check judges the code clang generates, where a destructor, a copy, a lambda and a template instantiation are plain calls. The six walks that hunted them go. The plugin reads the line directives from the preprocessor under the build's own flags, and the gate's raw-lexer run goes. Four reviews of the green step each found the next hole in the one place the check still read the tree, the virtual call. Now clang marks every vtable load, and the gate refuses an indirect call the tree does not explain. A call through the library's table of function pointers brings every function the table names.

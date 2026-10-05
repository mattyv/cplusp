# Where meaning can be lost

Oct 3, 2026. Status: gaps 1 to 4 have first results from the divergence battery, the rest is a skeleton. We fill a section only after we look at the gap, and where we can, run an experiment that shows it.

A proof is a statement about a model. It means something only if we can say exactly how the model relates to the bytes the compiler sees. This document lists every place on that path where meaning can leak, what we do about each, and what we still assume. Nothing in the proof layer is built until this document is complete.

## The path

```
C++ as the bot writes it
  → C++ as the compiler compiles it            (gap 1)
  → the gate's view of it                      (gap 2)
  → the translator's model of it               (gap 3)
  → the contracts, as written and as meant     (gap 4)
  → the trusted library contracts               (gap 5)
  → the prover and its solver                   (gap 6)
  → the verdict, mapped back to lines           (gap 7)
  → the bot, which writes the contracts          (gap 8)
```

## Gap 1: C++ as written versus as compiled

Partly open. Compiler version, flags, optimisation, implementation-defined behaviour, the target. The gate already refuses mismatched flags in two cases. One result from the battery, case `plain_int`: the width of `int` is implementation-defined. So the gate bans the built-in integer types in verified code. One assumption remains, and the skill states it: `size_t` maps to `uint64`. That is true on a 64-bit target only. The `stack_depth` case adds a second: a recursion bound in a contract holds on the target's stack, and the standard sets no minimum. The double model adds a third set, decisions 0020 and 0023. IEEE 754 binary64. Round to nearest even with gradual underflow. No fast math, no flush to zero, no x87 arithmetic, no fused multiply-add. No change of rounding mode at run time. The gate refuses the flags that break them, decision 0021, and requires `-std=c++23` and `-ffp-contract=off`. With `-p` the flags come from the compile database, and the gate does not read them yet. The other things the proof assumes about the build are not written down yet.

## Gap 2: the gate's view

Partly open. The gate does not see everything. Headers it does not judge, macros, `[[assume]]`, a `volatile` qualifier on a member function, anything after a `#if` the flags switch off. A construct that slips the gate and that the translator does not model must be refused by the translator, never skipped. That rule is not yet decided. The battery found three constructs the gate let through and the model got wrong. Plain `int`. A comparison of signed with unsigned. Two changes of state in one expression. Each is now a policy row with a sample pair. The case names the row. A pattern in the policy runs on the full tree. So it can match the implicit casts the compiler adds, and the `sign_compare` row relies on that. The gate is a list of spellings. A spelling it does not know passes, and C++ has many spellings for one operation. An outside review found nine in one sitting, decision 0025, a second found fifteen, and a third found four more. The lasting fix is a gate that refuses what it does not understand. Decision 0032 made the gate an allowlist of node kinds, and it is built. Every statement, expression, declaration and type kind that verified code may use is on a list in the policy. A kind outside the lists is refused with its name. The list was seeded from every gate-passing file and read kind by kind. The matchers and the hand-written checks now judge shapes inside allowed kinds, which is the one thing a kind cannot say. The rows still keep their counterexamples as tests, because a shape can hide inside an allowed kind. Parentheses, `auto`, a member, an alias, a mixed side effect, a functional cast with parentheses. All three reviews' holes are in the sample pairs. Some ceilings stay, and the code marks each with a `ponytail:` comment. A call through a template parameter has no callee the check can read. A reference member lets a const method change state. A line marker written in the source looks like the preprocessor's own. With the system flag or a pseudo name it hides every finding after it. So the gate reads the directives from the source text, in every spelling the preprocessor accepts, not from the output alone. A line of a raw string literal that starts like a directive or a pragma counts as one. In the root walk of decision 0033, a call through a function pointer has a fresh root. A reference returned by a function this translation unit does not define may reach any global, so the state check refuses a write through it. The state check reads a template body at its instantiation and a lambda body where the lambda is passed. It reads a destructor at the local that owns it, and a default member initialiser where the object is made. Attributes are not node kinds, so the allowlist keeps a list of them too, and a compiler builtin is a row. Two elements of one container in one call are one root, so an in-place swap is a copy out and two assignments. A run the gate cannot complete is refused, never reported as clean. One ceiling stays by design: a header behind `-isystem` is a system header, and the gate judges none of it. A build that puts a project directory there hides it from the gate. The upgrade is to refuse an `-isystem` path under the working directory.

## Gap 3: the model of C++

In progress. The divergence battery fills this gap case by case, decision 0017. No translator exists yet. A person writes the model by hand under the rules the battery finds. The rules are in `skills/cplusp-dafny/SKILL.md`. The record is `docs/mitigations-dafny.md`, one row per case, generated from the cases. Each case names the section of the C++ standard that decides it. A test runs Dafny, the gate and a witness under the sanitizer on every case.

The count and the verdicts live in `docs/mitigations-dafny.md`, one row per case. This document does not repeat them. The first round covered integer arithmetic, references, calls, loops, indexing and optionals. The second covered the conversions and the rest of arithmetic. Narrowing. Sign conversion. Promotion before widening. Shifts of a literal and of a signed value. Arithmetic on bool and enum class. Six naive models verified and were wrong in the first round. Most mitigations of the second round are gate rows, because the gate can refuse the form instead of the model carrying it.

A mitigation lives in one of four places: the model, the contract, the C++, or a gate row.

Floating point has its model, a real after one rounding per operation, decisions 0019 and 0020. The battery proved bounds for a sum, a cancellation, an increment, a division and two conversions. It found three faults: the axiom's lower limit, the fused multiply-add, and the missing contract spelling. Every row the policy allows or restricts now has at least one case, and the test `every_supported_row_has_a_case` keeps it so. The last round covered state. A trusted contract that omits `modifies` proves anything. A function-local static is a global. A global with a dynamic initializer runs in an open order across files. A torn read of a shared variable is a data race. The pinned toolchain, clang 18 with libstdc++ 13, does not compile `std::expected`, because the header asks for a concepts version clang 18 does not declare. The row allows it, and no example can show it until the toolchain moves. The model is of `double` only. The row `double_only` keeps `float` and `long double` out of verified code, decision 0024. A literal is exactly a double or the gate refuses it, decision 0027, because the model reads the real a literal spells. Recursion is the prover's, decision 0025. The state row came back to the gate, decision 0035. The gate reads the `modifies` and `reads` lines above a function, the one piece of contract it reads. It refuses an access to a global they do not list. The third review showed that a value model is exact only when no two names in one call reach one object. Decision 0033 makes that a gate rule, one root and one writer per call. It takes the clause `requires &a != &b` out of every contract, because a value has no address. Const reaches through a handle in every spelling of a write, not only a call. Beside an unordered change of state only a literal or an untouched local may stand. Dafny refuses a model that changes a field outside `modifies`, or a recursion without `decreases`. The battery proves the divergences a person imagined. The differential run, decision 0034, looks for the ones nobody did. It compiles the model and runs it beside the C++ on generated inputs. The naive model must part ways wherever the case says it is wrong. The match check that ties the C++ contract to the model is gap 4, the next piece.

## Gap 4: the contract language

First result, from case `signed_overflow` in the divergence battery. `a + b` in a contract is machine arithmetic. With `int32_t` modelled as Dafny's unbounded `int`, the function `add` verified. The C++ overflowed on INT32_MAX + 1 with undefined behaviour. With a bounded `int32`, Dafny refused the body and the contract. With the precondition the refusal demanded, it verified, and the caller carries the obligation. Rule: fixed-width types map to bounded types, never to `int`. Then Dafny checks every arithmetic step in a contract for overflow, as it checks the body.

The differential run, decision 0034, is the first match check. It ties the model to the C++ by their outputs on the same inputs, and says nothing about the contract. Six cases carry it. The aliasing cases cannot, because no input reaches `f(x, x)`.

Still open: the contract grammar. The cases write their `//@` contracts in an informal notation with `result`, `old(x)`, `modifies`, `mod`, `2^n` and `&a != &b`. The examples added forms the grammar must define. `&result == this` on a fluent return. `old(valid())` in a destructor. `this->field == x` on a member of a template type. `exists i :: P`. `modifies Tally::count` on a static data member. `result->version` through an optional. A `static_cast` inside a contract. Real division, `x / 1000.0`. A conditional, `c ? a : b`. Nothing parses it yet. Each form needs one meaning, written down, and a case in the battery. The `shift` case shows why. Dafny accepts a shift by the full width. A contract that copies Dafny's bound, `n <= 32`, admits a call that is undefined in C++.

## Gap 5: the trusted library contracts

Open. A contract for `vector::push_back` is an axiom. If it is wrong, every proof that uses it is wrong. How a contract is reviewed, how it is tested against the real library, and how a contradiction between two contracts is caught.

## Gap 6: the prover

Partly open. Solver bugs. Timeouts. Axioms and `assume` in trusted contracts. A precondition that can never be true makes every proof of that function trivial: a vacuous proof. The battery's `unlisted_modifies` case shows the other vacuity. A trusted contract with an `ensures` on a variable it does not list in `modifies` contradicts Dafny's frame. The caller then proves anything. How we detect vacuity is still open. Dafny is pinned at 4.11.0.

## Gap 7: the verdict

Open. The verdict names a line in a file. Which version of the file, under which flags, with which policy. A stale verdict is a false one.

## Gap 8: the bot

Open. The bot writes the contracts and can weaken them until the proof goes through. A `requires false` proves anything. What a human must review, what the tool must refuse, and what the caller's contract forces.

## Principles that fall out

We fill this as we close the gaps. Four candidates so far. The translator refuses what it does not model. Every proof must be able to fail, so every proved function gets a mutant the prover must reject. Contract arithmetic is machine arithmetic, with a range obligation on every operation. A mitigation that the C++ can carry becomes a gate row with a sample pair. Then the bot cannot write the divergent form at all.

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

Partly open. Compiler version, flags, optimisation, implementation-defined behaviour, the target. The gate already refuses mismatched flags in two cases. One result from the battery, case `plain_int`: the width of `int` is implementation-defined. So the gate bans the built-in integer types in verified code. One assumption remains, and the skill states it: `size_t` maps to `uint64`. That is true on a 64-bit target only. The other things the proof assumes about the build are not written down yet.

## Gap 2: the gate's view

Partly open. The gate does not see everything. Headers it does not judge, macros, `[[assume]]`, a `volatile` qualifier on a member function, anything after a `#if` the flags switch off. A construct that slips the gate and that the translator does not model must be refused by the translator, never skipped. That rule is not yet decided. The battery found three constructs the gate let through and the model got wrong. Plain `int`. A comparison of signed with unsigned. Two changes of state in one expression. Each is now a policy row with a sample pair. The case names the row. A pattern in the policy runs on the full tree. So it can match the implicit casts the compiler adds, and the `sign_compare` row relies on that.

## Gap 3: the model of C++

In progress. The divergence battery fills this gap case by case, decision 0017. No translator exists yet. A person writes the model by hand under the rules the battery finds. The rules are in `skills/cplusp-dafny/SKILL.md`. The record is `docs/mitigations-dafny.md`, one row per case, generated from the cases. Each case names the section of the C++ standard that decides it. A test runs Dafny, the gate and a witness under the sanitizer on every case.

Fourteen cases so far.

- Six naive models verified and were wrong. Signed division rounds the wrong way. A shift by the full width. A comparison of signed with unsigned. Plain `int`. Two references to one object. Two calls in one expression.
- Seven naive models failed, so the model was only stricter than the C++. Unsigned wrap. Promotion of `uint8_t`. A narrowing cast. A count-down loop on `size_t`. An index out of range. An empty optional. Signed overflow.
- One was a type error in Dafny. An integer used as a `bool`.

A mitigation lives in one of four places: the model, the contract, the C++, or a gate row.

Still to cover, one row of the policy at a time. The rest of arithmetic and the conversions. Floating point as opaque values. Object lifetime. Copies versus moves. Value and reference semantics. Inheritance and dispatch. Template instantiation. Containers and iterators. Algorithms with lambdas. Recursion. State. The test `every_supported_row_has_a_case` in `crates/divergence` keeps the list of rows without a case. That list shrinks to empty.

## Gap 4: the contract language

First result, from case `signed_overflow` in the divergence battery. `a + b` in a contract is machine arithmetic. With `int32_t` modelled as Dafny's unbounded `int`, the function `add` verified. The C++ overflowed on INT32_MAX + 1 with undefined behaviour. With a bounded `int32`, Dafny refused the body and the contract. With the precondition the refusal demanded, it verified, and the caller carries the obligation. Rule: fixed-width types map to bounded types, never to `int`. Then Dafny checks every arithmetic step in a contract for overflow, as it checks the body.

Still open: the contract grammar. The cases write their `//@` contracts in an informal notation with `result`, `old(x)`, `modifies`, `mod`, `2^n` and `&a != &b`. Nothing parses it yet. Each form needs one meaning, written down, and a case in the battery. The `shift` case shows why. Dafny accepts a shift by the full width. A contract that copies Dafny's bound, `n <= 32`, admits a call that is undefined in C++.

## Gap 5: the trusted library contracts

Open. A contract for `vector::push_back` is an axiom. If it is wrong, every proof that uses it is wrong. How a contract is reviewed, how it is tested against the real library, and how a contradiction between two contracts is caught.

## Gap 6: the prover

Open. Solver bugs. Timeouts. Axioms and `assume` in trusted contracts. A precondition that can never be true makes every proof of that function trivial: a vacuous proof. How we detect vacuity. Which prover versions are pinned.

## Gap 7: the verdict

Open. The verdict names a line in a file. Which version of the file, under which flags, with which policy. A stale verdict is a false one.

## Gap 8: the bot

Open. The bot writes the contracts and can weaken them until the proof goes through. A `requires false` proves anything. What a human must review, what the tool must refuse, and what the caller's contract forces.

## Principles that fall out

We fill this as we close the gaps. Four candidates so far. The translator refuses what it does not model. Every proof must be able to fail, so every proved function gets a mutant the prover must reject. Contract arithmetic is machine arithmetic, with a range obligation on every operation. A mitigation that the C++ can carry becomes a gate row with a sample pair. Then the bot cannot write the divergent form at all.

# Where meaning can be lost

Oct 3, 2026. Status: a skeleton. Each section is filled in only after we have looked at the gap, and where we can, run an experiment that shows it.

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

Open. Compiler version, flags, optimisation, implementation-defined behaviour, the width of `int`, the target. The gate already refuses mismatched flags in two cases. What else the proof assumes about the build has not been written down.

## Gap 2: the gate's view

Open. The gate does not see everything. Headers it does not judge, macros, `[[assume]]`, a `volatile` qualifier on a member function, anything after a `#if` the flags switch off. A construct that slips the gate and that the translator does not model must be refused by the translator, never skipped. That rule is not yet decided.

## Gap 3: the translator's model of C++

Open. Integer widths and overflow. Integral promotion in mixed arithmetic. Evaluation order. Short-circuit. References and aliasing. Object lifetime, constructors and destructors. Copies versus moves. Template instantiation. Floating point as opaque values. For each: what the model says, what C++ says, and how we show they agree.

## Gap 4: the contract language

Open. The first experiment is here. `a + b` in a contract: machine arithmetic that can overflow, or mathematical arithmetic that cannot? The two give different proofs for the same code. `old(x)`, `result`, quantifiers over containers, `reads` and `modifies`: each needs one meaning, written down, and a test that the translator keeps it.

## Gap 5: the trusted library contracts

Open. A contract for `vector::push_back` is an axiom. If it is wrong, every proof that uses it is wrong. How a contract is reviewed, how it is tested against the real library, and how a contradiction between two contracts is caught.

## Gap 6: the prover

Open. Solver bugs. Timeouts. Axioms and `assume` in trusted contracts. A precondition that can never be true makes every proof of that function trivial: a vacuous proof. How we detect vacuity. Which prover versions are pinned.

## Gap 7: the verdict

Open. The verdict names a line in a file. Which version of the file, under which flags, with which policy. A stale verdict is a false one.

## Gap 8: the bot

Open. The bot writes the contracts and can weaken them until the proof goes through. A `requires false` proves anything. What a human must review, what the tool must refuse, and what the caller's contract forces.

## Principles that fall out

To be filled as the gaps are closed. Three candidates so far. The translator refuses what it does not model. Every proof must be able to fail, so every proved function gets a mutant the prover must reject. Contract arithmetic is machine arithmetic, with a range obligation on every operation.

# 0019: Floating point stays in the subset on trial, modelled as a real after rounding

Date: 2026-10-03. Status: decided, as a trial. Decision 0020 will record the outcome.

## Decision

A C++ `double` is modelled in Dafny as a `real` after one rounding per operation. The rounding function is opaque. Three axioms are all the proof knows. A relative error of at most 2^-53 in the normal range. Exactness on integers up to 2^53. Monotonicity. Contracts on float results state error bounds, never equality. Inputs are required finite. The model lives in `divergence/dafny/Float.dfy`, and the battery's round C4 tests it.

Two gate rows go with it. `float_equality` bans `==` and `!=` on floats. `float_expression` allows one floating-point operation per expression, so the compiler cannot fuse two into one rounding.

## Why

Dafny has no floating-point type. Its `real` is exact, so a naive model proves `0.1 + 0.2 == 0.3`, which the hardware denies. The choices were to drop floats from the verified subset, to model them as bits, or to model them as reals with a rounding error. Bits would be a thousand lines of IEEE 754 in Dafny and proofs that run for minutes or time out. The real model is three axioms and verifies in seconds in the prototype.

## The trial

The round fails, and floats become `trusted_only`, on any of three signs. A mitigated model needs a hand lemma beyond the three axioms. A contract cannot be written as a bound a bot can read. An axiom cannot be justified against IEEE 754 round to nearest.

## What changes

The `floating_point` row's limit says finite values, bounds, and one operation per expression. The soundness map records what the model assumes about the build: IEEE 754 binary64, round to nearest even, no fast-math, no excess precision, no contraction. The gate cannot check those flags yet.

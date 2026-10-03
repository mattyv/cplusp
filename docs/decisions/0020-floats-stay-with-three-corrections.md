# 0020: Floating point stays in the subset, with three corrections to the model

Date: 2026-10-03. Status: decided. Closes the trial of decision 0019.

## Decision

The trial passed. Every mitigated float model verified with calls to the three axioms and nothing else, each in under a second of solver time. The equalities a bot would write all failed to verify, as they must. Floats stay in the verified subset under the `floating_point` row, modelled as a real after one rounding per operation.

The trial found three faults in the model, and the fix of each is part of this decision.

1. The error axiom was false for a product or quotient that underflows below the normal range, where the hardware's relative error is unbounded. The axiom now holds for zero and for the normal range only. A contract keeps results in that range with a lower magnitude bound as well as an upper one.
2. One operation per expression does not stop GCC from fusing a multiply and an add across statements. The gate requires `-ffp-contract=off`, decision 0021 amended.
3. A bound in real arithmetic had no spelling in the C++ contract. In a `//@` clause, float arithmetic is exact real arithmetic, `|x|` is the absolute value, and `eps` is 2^-53. A bound reads `|result - (a + b)| <= eps * |a + b|`. A magnitude bound the model needs is a `requires` in the C++ contract, never only in the model.

## Why

The alternative was `trusted_only`, which puts every float out of reach of a proof. The model proves bounds, not values, and that is what floating-point code can promise. The three faults were found by the battery, which is what it is for.

## What changes

`Float.dfy` carries the lower bound and a header that says what the gate requires. The gate requires `-ffp-contract=off`. The skill states the contract spelling. The soundness map lists the float assumptions under gap 1.

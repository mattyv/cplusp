# 0153: Each double operation carries its bound and its error

Date: 2026-10-17. Status: decided. Amends 0019, 0020 and 0023. The review of step two of doubles chose this shape.

## Decision

- In `divergence/dafny/Double.dfy`, each of `fadd`, `fsub`, `fmul` and `fdiv` requires that the magnitude of its exact result is at most `MAX`. `fdiv` also requires that its divisor is not zero.
- Each ensures the error of one rounding, `abs(f(a, b) - exact) <= EPS * abs(exact) + ETA`. Its body calls the axiom `RoundError` on the exact result.
- So a model calls the operation and nothing else. A model that does not keep the result below `MAX` fails at the operation, and so does a division by a value that may be zero.
- The axioms `round`, `RoundError` and `RoundExactInt` do not change.

## Why

Before this, the four operations required nothing. A model that forgot the call of `RoundError` had no bound on the exact result. So it could leave the range where C++ gives infinity, and still verify. With the bound on each operation, nobody can forget it, and the translator need not name the axiom. The review of step two showed that the 13 hand models that use the file verify unchanged. It also showed that the identity function satisfies both axioms, so they cannot prove false.

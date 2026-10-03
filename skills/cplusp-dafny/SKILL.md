---
name: cplusp-dafny
description: Rules for writing the Dafny model of a C+P function by hand, one rule per known divergence between C++ and Dafny. Use when writing or reviewing Dafny for cplusp.
---

# Writing Dafny for C+P

Every rule here was found by a case in `divergence/cases/`. The case shows the naive model, the divergence, and the mitigation. Follow the rules. When a construct has no rule, stop and write the case first.

## signed_overflow

Map `int32_t` to `newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000`, never to `int`.
Dafny then checks every arithmetic step for overflow, in the body and in the contract alike.
A sum that may overflow needs a precondition written with `as int`:
`requires -0x8000_0000 <= (a as int) + (b as int) < 0x8000_0000`.
The other mitigation is in the C++: add in `int64_t` and check the range before narrowing.

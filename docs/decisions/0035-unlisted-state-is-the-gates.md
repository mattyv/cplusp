# 0035: Unlisted state is the gate's, read from two comment lines

Date: 2026-10-05. Status: decided. Amends 0025, which moved the row `global_state` to the prover because no clang-tidy check read a contract. Settles the enforcement of 0011.

## Decision

The gate reads two kinds of contract line and nothing else: `//@ modifies a, b` and `//@ reads a, b`, the contiguous `//@` lines above a function. A check, `cplusp-unlisted-state`, collects every mutable global and static data member the function's body writes or reads. A call whose own lines list one counts as that access. A written one must be on the function's `modifies` line, and a read one on its `reads` or `modifies` line. Otherwise the gate refuses the access at its line under the row `global_state`. A constant is exempt. Members are implicit, decision 0028, and never listed.

## Why

Decision 0011 said globals and statics are listed in `reads` or `modifies`. Until now only the prover could notice a missing line, and only through the model. A trusted contract without `modifies` proved anything, which the battery case `unlisted_modifies` shows. The root walk of decision 0033 already knows what a function touches. Comparing that to two comment lines is a text scan, not a parser. It moves the fault from the model to the line where the C++ touches the state. The full contract reader waits. This piece does not.

## What changes

The row `global_state` returns to the gate with the check. A sample pair under `rules/global_state`. The battery case `unlisted_modifies` moves to the gate side, with the C++ under the rule in `fixed.cpp`. The soundness map and the skill say the gate reads these two lines. 77 rules, 64 enforced.

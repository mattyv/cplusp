# 0011: State enters contracts as inputs and outputs

Date: 2026-10-03. Status: decided on 2026-10-05. The gate check that reads the two clauses is the next round, decision to follow.

## Decision

Members are implicit through `this`, and a class may carry an invariant. Globals, statics, static members and function-local statics must be listed in the contract's `reads` or `modifies` clause. Constants are exempt. An unlisted access fails the gate.

## Why

A function that reads a global has an input its signature does not show. Naming it keeps proofs local: after a call, every unlisted global is known to be unchanged.

## What changes

The State section of the plan. The `global_state` row and the `cplusp-unlisted-state` check.

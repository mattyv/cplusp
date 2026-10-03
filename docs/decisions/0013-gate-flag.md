# 0013: When a row is the gate's

Date: 2026-10-03. Status: decided.

## Decision

A row is enforced by the gate when its stage is `gate`, or when it has a `detect` list and a decision other than `allow`. A row without a stage defaults to `none` only when it is an allow row with no checks, else to `gate`.

## Why

The first implementation exposed a contradiction: a prover row with a dormant detect was never enforced even after a team flipped it to ban. A ban row with no checks must fail validation, not vanish.

## What changes

The `gate` field of a rule in the core. Dormant rows carry a `use_instead` for the day they wake up.

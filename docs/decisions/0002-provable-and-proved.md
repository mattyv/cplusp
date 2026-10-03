# 0002: Provable is the gate's word, proved is the prover's

Date: 2026-10-03. Status: decided.

## Decision

The gate decides provable before any proof runs. A function is provable when it is in the verified set, uses only C+P features, and calls only contracted code. Proved is decided by the prover after it runs. Messages start with `Not provable:` or `Not proved:`.

## Why

The two words sound alike and were being used for both things. Each stage needs its own word so the bot knows which tool spoke.

## What changes

Every message prefix. The vocabulary section of the plan.

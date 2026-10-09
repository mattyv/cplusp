# 0087: Specify existing code with separate evidence of intent

Date: 2026-10-09. Status: decided. Extends 0086.

## Decision

Distinguish describing current behavior from checking intended behavior.
A specification inferred from code is a candidate until the reviewer accepts it as a requirement.
Use documentation, callers, tests and issue history to recover intent.
Record missing evidence and conflicts instead of inventing a requirement.

Map the verification boundary and preserve executable behavior during specification work.
Report suspected bugs separately. Do not silently repair code or exclude valid inputs to obtain a proof.
Draft public contracts, then supporting helper contracts and invariants.
Apply the fixed-contract mutation checks of 0086.

The reviewer resolves intent conflicts and approves contracts.
The coder implements against the approved contracts.
Hand off a table of requirements, intent evidence, contract clauses, proof status and remaining gaps.

## Why

A descriptive contract can faithfully capture a bug.
A proof of that contract establishes current behavior, but does not establish intended correctness.
Keep that distinction visible when applying verification to existing code.

## What changes

Add an existing-code workflow to the specification-review reference.
Add the trigger and entry point to the project skill.
This changes development guidance. It adds no translator feature.

# 0091: Validate C+P through increasingly complex programs

Date: 2026-10-09. Status: decided. Records the test plan, not completed runs.

## Decision

Test the complete coding workflow through the public C+P command and the compiled C++ executable.
Start with arithmetic, then sequence statistics, decimal parsing, sorted lookup and binary frame decoding.
Continue with recursive lookup, a bounded queue, a ledger, a limit order book and a replay application.

Each program has reviewed requirements, functional contracts and independent executable checks.
Exercise correct code, wrong bodies, weak contracts, unsupported constructs, agent repair and subsequent changes.
Keep proof outcomes separate from translation refusals, tool failures and specification-review findings.
A hand-written model is not an end-to-end pass.

Probe the required translator capabilities before each stage.
Record a missing capability as a blocker. Do not mark the central algorithm trusted to complete the stage.
Keep I/O and other trusted dependencies explicit in the proof scope.

## Why

Small programs isolate failures in the complete path.
Larger programs test composition, mutable state, diagnostics and changes to an existing verified program.
Independent executable checks can expose a mismatch between the proof claim and the shipped behavior.

## Execution

Use [the end-to-end validation plan](../end-to-end-validation-plan.md) for program scope and completion criteria.
Build the first batch around stages 1–3.
Implement the programs and runner in later changes. This decision records no new support or benchmark result.

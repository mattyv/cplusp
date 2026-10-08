# 0071: Requirements flow down, and completed proofs close component obligations

Date: 2026-10-08. Status: decided. Clarifies 0065 and 0066.

## Decision

Start with one feature's requirements, state invariants and component contracts.
Check that the contracts compose before committing to the implementations.
Implement and prove small increments, often starting with helpers.
Test difficult operations early against the current translator slice.

A caller proof can rely on a helper's contract before its implementation exists.
That proof remains conditional until the helper's implementation verifies.
Report open obligations. Claim a complete feature only when all relevant implementations and composition obligations verify.

The reviewer decides corrections to reviewed requirements and contracts, as in 0066.
Keep the C++ translation checks and independent executable tests.

## Why

SPARK supports contracts and analysis before implementation.
Dafny supports abstract interfaces and refinement.
These methods allow early composition checks and incremental implementation.

## What changes

Update the Whole-program development section of the C+P Dafny skill.
Add a sort-then-search example and explain conditional caller proofs.
This changes development guidance. It adds no translator feature.

See [the research report](../research/formal-verification-llm-coding-report.md) for sources and evidence limits.

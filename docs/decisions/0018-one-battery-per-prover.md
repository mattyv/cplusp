# 0018: One divergence battery, one skill and one mitigation report per prover

Date: 2026-10-03. Status: decided.

## Decision

Each verification language gets its own battery of divergence cases, its own skill for the LLM, and its own generated mitigation report. The first set is Dafny's: `divergence/dafny/cases/`, `skills/cplusp-dafny/SKILL.md`, `docs/mitigations-dafny.md`. VeriFast, or any later prover, gets a sibling set with the same shape. The battery test and the report generator take the language directory as their argument.

## Why

A divergence is between C++ and one prover's model of it. Dafny's Euclidean division is not VeriFast's concern, and VeriFast's ownership rules are not Dafny's. Mixing them in one list would hide which rule applies to which prover.

## What changes

The paths above. The C++ side of a case, and a mitigation that lands on the gate as a policy row, is shared by every prover, so a case may be copied between batteries with only its model files changed.

# 0086: Generate specifications in components and challenge fixed contracts

Date: 2026-10-09. Status: decided. Extends 0066 and 0071.

## Decision

Derive candidate specifications from requirements, callers, examples and code.
Separate intended behavior from observed behavior. Review the candidate before the coder implements it.
Generate supporting contracts and invariants in dependency order.
Keep reviewed contracts fixed during proof repair.

The reviewer checks deliberately wrong bodies against fixed contracts and specification definitions.
Record a witness and the verifier outcome for each variant.
Distinguish proof rejection from translation refusal, syntax failure, timeout and tool failure.
Check that preconditions admit intended inputs. Report surviving wrong variants.
These checks assess specification strength. They do not establish completeness.

Compare executable behavior before and after annotation work.
Keep translation fidelity and independent executable tests as separate checks.
Keep the reviewer and coder roles of 0066.

## Why

SpecSyn provides measured evidence for decomposition and mutation refinement in C/ACSL.
AutoSpec+ provides evidence for verification-guided specification repair.
KVerus provides reusable Verus workflow stages. Its published evaluation concerns an earlier proof-generation workflow with supplied specifications.
The current skill pack has no isolated specification-quality result in that study.

## What changes

Add a specification-review reference to the existing C+P skill.
Connect it to the reviewer and coder instructions.
Update both versions of the research report.
This changes development guidance. It adds no translator feature or verification dependency.
Measure the local effect with held-out tasks before claiming a C+P improvement.

See [the research report](../research/formal-verification-llm-coding-report.md) for sources and measurement limits.

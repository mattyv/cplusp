# 0065: Requirements, contracts and composition guide verified development

Date: 2026-10-08. Status: decided.
Extends the modelling skill with a whole-program workflow.
Preserves the translator architecture of 0056 and the value model of 0029.

## Decision

Start with the subsystem requirement.
Derive component contracts, types and state effects from it.
Review the contracts before relying on them.
Prove component bodies and caller obligations.
Prove that the composition establishes the subsystem requirement.

Check initialization, public entry points and dependency assumptions.
Validate the correspondence between C++ and Dafny.
Report translation acceptance, proof outcome and executable tests separately.
A hand-written model does not extend automatic translator support.

Do not weaken contracts or add assumptions merely to make proofs pass.
Report requirement changes and exclusions for review.

## Why

The [research report](../research/formal-verification-llm-coding-report.md) records evidence that reliable contracts and decomposition improve measured agent results.
SPARK provides a documented method for modular development.
Dafny supports the same contract-based composition.
C+P also needs evidence that translation preserves C++ behavior.

These findings do not establish C+P's production defect reduction or lifetime cost savings.
Measure its practical payoff with the pilot described in the report.

## What changes

The repository stores the research report as Markdown and HTML.
The [FAQ](../formal-proof-faq.md) explains proof guarantees and limits.
The [modelling skill](../../skills/cplusp-dafny/SKILL.md) adds the development workflow.
No translator rule or policy row changes.

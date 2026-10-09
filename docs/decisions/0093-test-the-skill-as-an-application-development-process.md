# 0093: Test the skill as an application development process

Date: 2026-10-09. Status: decided. Extends 0091 and 0092.

## Decision

The application ladder tests both C+P tooling and the complete skill process.
Start process runs with an application brief. Let the agents derive specifications and module boundaries through the prescribed roles.
Do not give them finished contracts and claim that specification generation works.

Assess requirements, decomposition, specification review, incremental proof, integration, adversarial review and maintenance.
Record the output and failures of each step, the skill revision, total cost and extra assistance.
Measure process conformance separately from independent application correctness.
Classify a tool blocker separately from a process violation or false claim of completion.

Compare the complete skill process with ordinary coding and tests under equal starting information and budgets.
Keep the separate comparison that gives both arms reviewed contracts to assess proof feedback.
Pin the skill during measured batches. Evaluate revisions on held-out tasks.

## Why

A working prover cannot establish that the development method produces adequate specifications or manageable module boundaries.
The method must also survive integration, changes and a handoff to another agent.
The user wants evidence for that process at increasing application sizes.

## Execution

Use [the validation plan](../end-to-end-validation-plan.md) for the process steps and measurements.
The first measured application process run follows the toy tool check.
This decision records no process-evaluation result.

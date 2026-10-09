# 0092: Test application scale as well as proof complexity

Date: 2026-10-09. Status: decided. Amends the program order and first batch of 0091.

## Decision

Use six application milestones: a toy arithmetic program, telemetry analyzer, inventory/order application,
indexed key-value store, matching engine and exchange simulator.
Increase the intended application scale from tens of lines through thousands to tens of thousands.
Keep the smaller algorithms of 0091 as components, feature probes and regression cases.

Keep the end-to-end checks of 0091: automatic translation, proofs, executable checks, wrong variants, agent repair and subsequent changes.
Report verified core size separately from total application size and trusted I/O.
Measure verification after body, contract and shared-type edits, as well as full verification.
Keep missing translator capabilities as explicit stage blockers.

## Why

The first ladder increased proof difficulty while most programs remained similar in size.
The user wants larger programs to test application-scale composition and maintenance.
The new ladder makes that objective explicit.

## Execution

Use [the revised validation plan](../end-to-end-validation-plan.md) for scope, scale bands and order.
Run the toy first, then the telemetry application. Qualify mutation support before the inventory application.
The size bands are planning estimates. Do not pad source to reach them.
This decision records no completed application runs or new translator support.

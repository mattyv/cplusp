# 0015: Build the gate and nothing past it

Date: 2026-10-03. Status: decided.

## Decision

The build stops at the gate: the policy commands and `cplusp gate`. No prover, translator or clang-tidy plugin work until asked.

## Why

One piece at a time, proved and reviewed, before the next.

## What changes

The plan's phases past the gate stay as plans.

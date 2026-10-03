# 0010: How we work

Date: 2026-10-03. Status: decided.

## Decision

Failing test first, always. Proofs are part of the deliverable, not an add-on. The ponytail ladder governs every change: laziest working solution, fewest files, no abstractions nobody asked for, a `ponytail:` comment on any deliberate corner. Sonnet agents implement. Fable reviews. Docs follow Simplified Technical English and are linted.

## Why

One proof after another is how the quality gets high by the end. Sonnet for the grunt work keeps the expensive model on the decisions and the review.

## What changes

CLAUDE.md. Every commit is a red step or a green step. This log.

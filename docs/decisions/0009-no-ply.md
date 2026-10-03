# 0009: Ply is not a dependency for now

Date: 2026-10-03. Status: decided.

## Decision

cplusp does not use ply. Verus in the source is the proof instrument.

## Why

Ply's Verus route proves a shadow of the code, not the source, and ply is alpha. Two of its jobs fit later: fuzzing the untrusted edges and drawing the proved-versus-not picture of cplusp itself.

## What changes

Nothing today. Ply's working rules (failing test first, assert the outcome, one invariant test over spot checks, goldens reviewed) are adopted in CLAUDE.md.

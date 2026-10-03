# 0004: No undefined behaviour in verified code

Date: 2026-10-03. Status: decided.

## Decision

A verified function has no undefined behaviour. UB that lives in a construct is the gate's job. UB that depends on values is the prover's job. Every row of the subset table records which stage guarantees it.

## Why

The two stages were described by mechanism. This describes them by the promise they make.

## What changes

A Stage column. New rows: `[[assume]]`, `unreachable`, `longjmp` banned. The `memcpy` family, `std::launder` and placement new trusted only.

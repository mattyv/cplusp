# 0008: The driver is Rust written in Verus

Date: 2026-10-03. Status: decided.

## Decision

The clang-tidy module is C++ because it must be. Everything else is Rust, written in Verus from the start, one static binary. No Python anywhere. TypeScript is not in the core. Dafny is a prover candidate, not an implementation language.

## Why

We prove as much of our own tooling as the tools allow. Verus proves Rust source directly and the proved code is ordinary Rust after erasure. Dafny would need glue in another language for every file read and every process it starts.

## What changes

A pinned Rust toolchain. `cargo verus verify` must pass before a commit. The shell is a thin trusted edge and is listed as such.

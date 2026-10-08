# 0082: Hex literals, exists, and several bound names

Date: 2026-10-08. Status: decided. Amends 0064 on the contract language.

## Decision

- A contract reads an integer in hex, such as `0x7FFFFFFF`, as C++ writes it. The digit separator `'` and the suffixes `u`, `l`, `ul`, `ll` and `ull` in any case are allowed. The value is the exact integer, as each integer of a contract is, decision 0060. A value that does not fit `uint64_t` is refused.
- `exists j :: P` binds `j` to an exact integer in `P`, as `forall` does, decision 0064. It is `exists j: int :: P` in Dafny.
- `forall i, j :: P` and `exists i, j :: P` bind each name in order. They are `forall i :: forall j :: P` and the same for `exists`.
- `/` and `%` in a contract still have no rule. C++ divides toward zero, and Dafny divides so that the remainder is never negative. They need their own decision, with the battery case `signed_division`.

## Why

The sweep of the examples after `radix_find` found contract lines that the translator could not read. Most of them hold a hex bound, an `exists` or `forall i, j`. Each one is a small step in the parser.

## What changes

The shell reads hex literals. The core gains `exists` and a list of bound names after `forall` and `exists`. The shell prints `exists`.

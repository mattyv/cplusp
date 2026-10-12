# 0139: `at` of a read-only sequence is an index

Date: 2026-10-12. Status: decided. Amends 0064.

## Decision

- In code, `v.at(i)` of a read-only sequence is `v[i]`, decision 0064. That covers a const vector and a const std::array. Dafny proves that each index is in range.
- In C++, `at` throws when the index is out of range. Proved code never reaches that case, so the throw cannot happen, and the model needs no exception.
- In a contract, `at` has no rule. A contract reads `v[i]`.

## Why

The survey of the examples that do not prove found that `containers` stops only at `v.at(i)`. The argument is the one of 0131 for `*o` and `value()`. The prover discharges the check, so the two forms are equal on every input that the contract allows.

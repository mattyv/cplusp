# 0026: Two changes of state in one expression are allowed only where the standard orders them

Date: 2026-10-04. Status: decided. Amends the limit of the row `evaluation_order`.

## Decision

A full expression may change state twice only where C++ orders the two changes. The standard orders the right side of an assignment before the left. It orders the operands of `&&`, `||`, the comma and `?:`, and the arguments of a call before its body. Since C++17 it orders the operands of `<<`, `>>` and `[]`. It does not order the arguments of one call among themselves, nor the operands of an arithmetic or comparison operator. A check in the plugin, `cplusp-evaluation-order`, applies this, and a call into `std` counts like any other.

## Why

The row said "at most one change" and its pattern enforced something else: no two state-changing calls outside `std`. The review showed both sides of the gap. `before(next(x), x++)` passed, and clang and GCC give it different answers. Two `std::exchange` calls passed. `c ? next(x) : next(x)` was refused, and it has one order. A pattern cannot count side effects through sequencing. A check can, and the rule it applies is the standard's own.

## What changes

The row's limit and its detect. The sample pair carries the review's three cases. The plugin gains the check, decision 0016 extended.

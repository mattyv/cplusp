# 0074: A non-const reference to a struct has no rule yet

Date: 2026-10-08. Status: decided. Amends 0073.

## Decision

A struct is in the subset as a parameter by value or by const reference. A non-const reference to a struct is refused by its type. It can carry a write out of the function, and the model reads a struct as a value in only.

## Why

The green step of 0073 also took `Point&` as a struct. A callee that writes through it has its body refused, but its signature is in the subset, so its callers can call it. Then a caller reads the struct as the same value after the call, and proves a false contract. The refusal of the callee fails the run, but the proof of the caller is still wrong. A write through a reference waits for a rule of its own, a value in and a value out as 0029 says.

## What changes

The plugin writes a struct type only by value or by const reference.

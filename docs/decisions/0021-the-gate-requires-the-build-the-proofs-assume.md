# 0021: The gate requires the build the proofs assume

Date: 2026-10-03. Status: decided.

## Decision

The gate reads the compiler flags before it judges a file, and refuses a build the proofs cannot follow. Three kinds of flag are refused. A flag that changes floating-point results, such as `-ffast-math` or `-Ofast`, because the float model assumes IEEE 754 round to nearest. A `-std` below C++20, or none, because the proofs cite C++20. A flag that hides a compiler warning the policy names, such as `-w` or `-Wno-unsequenced`, because that hides a row of the gate.

## Why

The battery found constructs that C++20 defines and C++17 leaves undefined: a signed value shifted left, and a large value narrowed into a smaller signed type. The proofs rest on the C++20 answers. A team that compiles as C++17 could get a proven function that misbehaves there. The same holds for fast math, which lets the compiler change float results. A silenced warning turns a gate row off.

## What changes

Three refusals in the gate, each with its own test. The soundness map's gap 1 lists the flags. With `-p` the flags come from the compile database, and the gate does not read them yet.

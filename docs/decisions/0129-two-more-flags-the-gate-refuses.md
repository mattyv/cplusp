# 0129: Two more flags that the gate refuses

Date: 2026-10-11. Status: decided. Amends 0022 and 0128.

## Decision

- The gate refuses `--no-warnings`. It is the long form of `-w`, so it hides each warning that the policy names.
- The gate refuses the bare flag `--std`. Its value is the next flag, as in `--std c++20`. The gate does not read that value, so a `-std=c++23` that the gate sees can stand next to a C++20 build.
- The core proves both refusals with the other facts of a run with no refusal, decision 0128.

## Why

The review of 0128 found both. With `--no-warnings`, a sample that the gate refuses passed with no finding. With `--std c++20`, the compiler built the file as C++20, and the gate passed it. Each refusal is safer than the old behaviour, and no example uses either flag.

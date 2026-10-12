# 0136: An array of bool stays out

Date: 2026-10-12. Status: decided. Amends 0132.

## Decision

- `std::array<bool, N>` stays out of the subset, as every sequence of bool does. Decision 0132 said that it was in. The core refuses each sequence of bool with `an optional of a struct or a sequence of bool has no rule yet.`, and that refusal stays.
- The function of `model-array.cpp` that read an array of bool moves to `model-array-refuse.cpp`, where the core refuses it.

## Why

The coder found that the green step of 0132 could not meet its test. Decision 0132 said that the core does not change, and the core refuses a sequence of bool. To take an array of bool is a change to the core for no example that needs it. The smaller subset is the safer one.

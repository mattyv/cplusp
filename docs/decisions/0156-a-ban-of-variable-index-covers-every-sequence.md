# 0156: A ban of variable_index covers every sequence

Date: 2026-10-18. Status: decided. Amends 0139 and the row `variable_index` of the policy.

## Decision

- The row `variable_index` is `allow`, so its checks are dormant, and the prover proves each index. A team can ban the row. Then the gate refuses a variable index into an array, a `std::vector`, a `std::array` and a `std::span`. It also refuses a call of `at()` with a variable index, decision 0139.
- A constant index stays allowed under the ban. A constant is an integer literal or a `constexpr` variable. Any other index is a finding, `v[1 + 1]` too, which refuses more and never less.

## Why

The detect of the row named one check, `cppcoreguidelines-pro-bounds-constant-array-index`. That check sees only an index into a C array or a `std::array`. So a team that banned the row still got `v[i]` on a vector, `s[i]` on a span and `v.at(i)`. The row did not mean what it says.

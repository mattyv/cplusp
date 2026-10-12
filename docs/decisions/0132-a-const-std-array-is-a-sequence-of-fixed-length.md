# 0132: A const std::array is a read-only sequence of fixed length

Date: 2026-10-12. Status: decided. Amends 0064 and 0070.

## Decision

- A parameter of type `const std::array<T, N>&` or `const std::array<T, N>` is a read-only sequence with the fixed extent `N`, as `std::span<const T, N>` is in 0070. Its method requires `|v| == N`. `T` is a scalar type of the subset or a plain struct, as for a span.
- `std::array<bool, N>` is in the subset. It has no proxy, unlike `std::vector<bool>`.
- An array with no `const`, by value or by reference, stays out of the subset. A field of type `std::array` also stays out.
- The plugin writes the type. The core and the shell do not change.

## Why

The survey of the examples that do not prove found that `array_span` stops only at `const std::array<int32_t, 4>&`. The core already proves a sequence of fixed length, decision 0070. An array of `const` gives reads only, decision 0040, so its value stays the same for the whole call, and the value model of 0064 holds.

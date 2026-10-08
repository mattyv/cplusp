# 0064: The fourth slice: read-only sequences, `forall` and chained comparisons

Date: 2026-10-08. Status: decided. Amends 0057 on the fourth slice. Structs, `std::optional` and recursion move to the fifth.

## Decision

- A parameter of type `std::span<const T>`, `const std::vector<T>&` or `const std::vector<T>` is a Dafny `seq<T>`, when `T` is a scalar type of the subset. Nothing in the subset writes, and a const view gives reads only, decision 0040. So the value of the sequence stays the same for the whole call.
- A sequence is in the subset only as a parameter. A local, a return value or a mutable view of a sequence has no rule yet. `std::vector<bool>` has no rule, because its elements are proxies.
- Each method with a sequence parameter requires that the length fits `size_t`. That holds for every C++ sequence, and Dafny needs it to cast the length to `uint64`.
- In code, `v.size()` is `(|v| as uint64)` and `v[i]` is `v[i]`. Dafny proves that each index is in range, so code that reads out of range does not prove. C++ gives undefined behaviour there.
- In a contract, `v.size()` is `|v|` on the exact integers, and `v[e]` is the element, read as an exact integer when it is one. `forall j :: P` binds `j` to an exact integer in `P`. A chain of two comparisons in one direction, such as `0 <= j < n`, means both comparisons, as in Dafny.

## Why

`find` in `examples/control_flow` reads a `const std::vector<int32_t>&` by index in a loop, and its contract needs `forall` and a chain. `checksum` and `radix_find` read a `std::span<const uint8_t>`. A read-only sequence is the smallest step that reaches them.

## What changes

The core gains the sequence type, length, index, `forall`, chains, and the bound on the length. The parser reads `[`, `]`, `.size()`, `forall` and `::`. The plugin writes the sequence types, `size()` and `operator[]`. The shell prints `seq<T>`, `|v|`, `v[i]` and the quantifier.

# 0085: Slices in a contract

Date: 2026-10-09. Status: decided. Amends 0064 on the contract language.

## Decision

- In a contract, `v[i..j]`, `v[..j]` and `v[i..]` read a part of a sequence on a path, as in Dafny. `v[i..j]` holds the elements from `i` up to `j`, and `j` is not in it. Dafny proves that `0 <= i <= j <= v.size()` holds where the contract reads the part.
- A part is a sequence of the same element, with no fixed extent. A contract can read its `.size()`, an element and `.empty()`, and it can pass the part to a function of the companion file.
- Code has no slice. C++ has no such form, and `subspan` is the form of code, decision 0078.

## Why

The examples `recursion`, `checksum` and `dot_product` state their result with a function of a part of a sequence, such as `Count(v[i..], x)`. The model of `recursion` with a part was checked by hand in Dafny.

## What changes

The parser reads `..` inside `[` and `]`. The core gains the part of a sequence on a path. The shell prints it.

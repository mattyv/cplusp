# 0078: subspan and empty

Date: 2026-10-08. Status: decided. The fifth step of the fifth slice in 0072.

## Decision

- In code and in a contract, `v.empty()` reads a sequence on a path. It is `|v| == 0`.
- In code, `s.subspan(k)` on a `std::span` is `s[k..]`. Dafny proves that `k` is at most the length. C++ gives undefined behaviour when `k` is larger, so code that relies on it does not prove.
- The value of `s.subspan(k)` passes to a sequence parameter of the same element and of no fixed extent. A copy does the same in 0070. A span of fixed extent gives a span of no fixed extent here, as in C++.
- `subspan(k, n)`, `first(n)`, `last(n)` and `subspan` in a contract have no rule yet.

## Why

`radix_find` asks `key.empty()` and recurses with `key.subspan(n.children[i].prefix.size())`. These are the last two reads of a sequence that it needs.

## What changes

The core gains `empty` in code and contracts, and `subspan` with one argument in code. The parser reads `.empty()`. The plugin writes both. The shell prints `|v| == 0` and `v[k..]`.

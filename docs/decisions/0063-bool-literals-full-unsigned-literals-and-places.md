# 0063: Bool literals, literals over the full unsigned range, and a refusal at the right file

Date: 2026-10-08. Status: decided. Amends 0060 and 0061 after a second outside review.

## Decision

- `true` and `false` in code are bool literals, and they print as `true` and `false` in Dafny.
- A literal in code or in a contract holds a value from 0 to 2^64 - 1. C++ writes no negative literal, because a minus is an operator of its own. So each `uint64_t` value has a literal, such as `18446744073709551615ULL`.
- The plugin writes the file of each contract line. The shell gives the core one number for each pair of a file and a line. The core never computes with a line, so this changes nothing in the core. Then a refusal of a contract line in a header names the header, and the line in it.

## Why

A second outside review of slice 3 found three gaps. `bool` was a type of the subset, but `return true;` was refused. `18446744073709551615ULL` was refused, because the plugin and the core held a literal in 63 bits. An invalid contract line in a header was reported at the same line number in the source file. So it sent the repair to the wrong file.

## What changes

The core gains a bool literal, and its literals become unsigned 64-bit numbers. The plugin writes bool literals, literals of 64 bits, and the file of each contract line. The shell keeps a table of places in place of bare lines.

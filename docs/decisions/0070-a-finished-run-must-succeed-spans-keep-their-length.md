# 0070: A run of Dafny must finish and succeed, a span keeps a fixed length, and a sequence passes to a sequence parameter

Date: 2026-10-08. Status: decided. Amends 0064 and 0069 after a third outside review.

## Decision

- `prove` says `ok: proved` only when Dafny exits 0 and its summary says `0 errors` with no time-out. A run of Dafny that fails with no error line that `prove` can read is a fault of the tool. A summary that disagrees with the exit status is also a fault of the tool. In both cases `prove` prints `dafny failed` and the output on stderr, and exits 2.
- A `std::span<const T, N>` with a fixed extent keeps its length. Its method requires `|v| == N`, in place of the bound of 0064. So `v.size()` is `N`, and `v[0]` is in range when `N` is more than 0.
- A sequence made from one sequence keeps its value. That covers a copy of a span and a span made from a const vector. It also covers a span with no fixed extent made from one with a fixed extent. The element types must be the same. The new sequence must have no fixed extent, or the same extent as the old one. A sequence of a fixed extent made from one of another length is refused, because its length can change.
- The cast that the compiler writes around such a construction keeps the value. The construction itself is what the core judges.

## Why

The review used a stand-in for Dafny that printed `finished with 0 verified, 1 error` and exited 4. `prove` said `ok: proved`, because it read only the error lines and the presence of a summary. It found that `std::span<const int32_t, 3>` lost its length, so a true contract on `v.size()` failed. It found that a span passed by value to a span parameter was refused, so two functions that each translate could not call each other.

## What changes

The core gains the extent of a sequence, the bound of a fixed extent, and a rule for a sequence made from a sequence. The plugin writes the extent and the construction. The shell checks the exit status and the counts of the summary.

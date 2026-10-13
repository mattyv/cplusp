# 0146: The author states the length of a vector after the call

Date: 2026-10-13. Status: decided. Amends 0145.

## Decision

- The translator adds no contract line about the length of a vector by reference. An ensures line that reads `v[i]` after the call needs a line before it that gives the length, such as `ensures v.size() == old(v.size())`. Without it, the prover says that the index may be out of range.
- A loop that writes the vector needs the same fact as an invariant, when a line after the loop reads the length.
- The fixture `model-vec-ref.cpp` gets this line in `swap_at`.

## Why

The body only writes elements in step one of 0145, so the length stays the same. But Dafny does not see this from outside the body. It sees only the ensures lines. A line that the translator adds would need a twin in each loop. Step two adds `push_back`, which changes the length, so that line would have to go again. The extra line costs the author one line, and the examples already have it.

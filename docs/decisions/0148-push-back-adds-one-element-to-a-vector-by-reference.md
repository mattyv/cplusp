# 0148: push_back adds one element to a vector by reference

Date: 2026-10-14. Status: decided. Amends 0145 and 0146. The user chose this direction on 2026-10-13.

## Decision

- In code, `v.push_back(e)` on a vector by reference of 0145 is a statement. It gives `v' := v' + [e]`. The value `e` holds no call. A call in it is refused as out of place.
- `push_back` can fail. It throws when it cannot get memory or when the vector is at `max_size()`. Verified code has no `try`, so a failed `push_back` never returns to verified code. The proof covers each return, as the plan says for allocation: allocation is trusted. The model lets the vector grow past `max_size()`, so it holds more runs than C++ has. So a proof over the model holds for each run of C++ that returns.
- A read of `v.size()` in code is `|v'|` as `size_t`, so Dafny proves that it fits.
- The author states the new length in an ensures line, as 0146 says, such as `ensures v.size() == old(v.size()) + 1`.
- A contract that compares the elements of two vectors as a multiset names a predicate of the companion file. The translator adds no `multiset` form to the contract. The example `sorted_insert` has `AddsOne` and the lemma `Inserted`.
- These still have no rule: `emplace_back`, `pop_back`, `insert`, `erase`, `resize`, `clear`, `reserve` and `assign`.

## Why

The example `sorted_insert` appends with `push_back`, then moves the new element down. With this rule and invariants in the C++, it proves. A test run proved the same model 20 times in 20. Invariants on each element held in each run. An invariant that compared two slices failed in one run of ten, so the example states each element.

Dafny cannot see alone that the final write gives the old elements and `x` as a multiset. A lemma of the companion file states it, and an apply line calls the lemma above the final write. An apply line below the last statement is refused, decision 0099.

# 0161: std::sort of a vector of integers. Slice two of 0160

Date: 2026-10-19. Status: decided. Amends 0149 on the calls of std algorithms. This is slice two of 0160.

## Decision

- `std::sort(v.begin(), v.end())` sorts the whole of `v`, with the default `<`. Here `v` is a local vector of 0160 or a vector by reference of 0145, and its elements are integers. The model writes `v := StdSort(v, (a: T, b: T) => a < b);` with `StdSort` of `divergence/dafny/Algorithm.dfy`. For a vector by reference, the place is the value after the call, `v'`.
- `<` on integers is a strict weak order, so Dafny proves the requirement of `StdSort` at the call with no help.
- After the call, the model knows three facts. `v` has the same multiset of elements and the same length, and no later element is below an earlier one. A contract that needs more, such as the smallest element of the old vector, names a lemma of the companion file with `//@ apply`, decision 0099. The lemma can read `SortedBy` and `StrictWeakOrder` of the module.
- When the model calls `StdSort`, `prove` prints the line of 0160 once, before its verdict. The model holds the module `Algorithm` from `divergence/dafny/Algorithm.dfy`, as it holds `Double` in 0154.
- A sort of a read-only sequence is a write to a parameter, and the translator refuses it with that sentence. A sort of a vector of a struct needs a comparator, slice three.
- The translator refuses any other form of `std::sort`, such as a part of a range, a comparator or an execution policy. Its sentence is `std::sort of another form: the translator has no rule for it yet.` Other sorts, such as `std::stable_sort` and `std::ranges::sort`, stay calls with no model.
- The companion file cannot declare `Algorithm`, `StdSort`, `StrictWeakOrder` or `SortedBy`, decision 0083.
- The battery verifies `Algorithm.dfy` on its own. It also checks that a comparator that is not a strict weak order fails at the call.

## Why

The example `algorithms` sorts a copy and reads its first element. The model of 0160 keeps the trust in the contract of `StdSort` alone, and Dafny checks that an insertion sort meets that contract. The sentence for another form names `std::sort`. Before, the refusal named a type of the library, with the iterators of libstdc++, and a bot cannot act on it.

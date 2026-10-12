# 0131: A chain of more than two comparisons, and `*` on an optional in a contract

Date: 2026-10-12. Status: decided. Amends 0064 and 0075.

## Decision

- In a contract, a chain of three or more comparisons, such as `0 <= i < j < n`, means each comparison, as in Dafny. The parser reads it as the chains of two that overlap, joined by `&&`. So `0 <= i < j < n` is `(0 <= i < j) && (i < j < n)`. Each chain of two keeps the rules of 0064: one direction, and no enumerator. A chain with two directions anywhere in it is refused.
- The parser reads a shared term again from the same tokens, up to three times, so the copies are equal. It needs no copy function. The cost grows with the depth of chains inside chains, and contract lines are short.
- The proof of the parser says only that it reads tokens in order and gives no unknown node. It does not say that the chain has the right meaning. The tests in `crates/cplusp-core/tests/model.rs` and the fixtures `model-chain*.cpp` hold that. The review made three wrong parsers: `||` in place of `&&`, chains that do not overlap, and `has_value` in place of `value`. Each one still proves, and the tests refuse each one. A spec of the parser over the tokens is the upgrade.
- In a contract, `*o` is `o.value()`, decision 0075. Dafny proves that the optional holds a value wherever the contract reads it. So a contract that reads `*o` without a test of `o.has_value()` does not prove, and the prover says that the optional may be empty here.
- `*p` on anything that is not an optional stays refused, with the same message as before.

## Why

The survey of the examples that do not prove found these two forms as the first block in three examples. `binary_search`, `sorted_insert` and `sort_with_comparator` state that a sequence is sorted with `0 <= i < j < n`. `binary_search` and `optional_expected_variant` read the answer with `*result`. The rewrite `0 <= i && i < j < n` works today, but the example states the plain form, and Dafny reads it.

The overlapping chains keep the rules of a chain in one place. A new node for a chain of any length would need a new rule in each pass of the translator.

`*` on an empty optional is undefined behaviour in C++, and `value()` throws. A contract that proves never reads an empty optional, so neither difference can show.

The chain does not make an example prove by itself. Each of the three examples meets another block after it: a temporary, a vector by reference, or a vector of structs. The function `binary_search` alone, without `contains`, now proves, and so do `half_of_even` and `half_or` in `optional_expected_variant`.

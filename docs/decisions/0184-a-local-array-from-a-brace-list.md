# 0184: A local array from a brace list

Date: 2026-10-24. Status: decided. Builds on 0064, 0070, 0132, 0160 and 0175. The example `strings` builds the four bytes of "GET " in a local `std::array` and passes it as a span.

## Decision

A local `std::array<T, N>` whose start value is a brace list of `N` values is the sequence of the values. The values run in order, first to last, as C++ runs the values of a brace list. The code reads its elements and its size, and passes it to a sequence parameter. A write to an element is a new value of the local, as for a local vector, decision 0160. The length stays the same.

These forms have no rule:

- a brace list with a count that is not `N`. It keeps the sentence of 0175: "a braced list of m values for a std::array of n: the translator has no rule for it yet."
- a local `std::array` with any other start value, or with no start value. It keeps the sentence "a sequence is in the subset only as a parameter."
- a local `std::array` of a struct with a destructor. It keeps the sentence of 0178: "a copy of a struct with a destructor: the translator has no rule for it yet."

## Why

A short table of constants is a common form. Decision 0175 already reads `return {a, b, c};` of a std::array as the sequence of the values. A local built the same way is the same sequence, with a name.

## What changes

The core reads a local `std::array` with a brace list as a Dafny local of a sequence literal. It checks the count against the extent. The plugin already writes the local and the brace list. It now also writes `t[i] = e` of a local `std::array` as a write to an element, as for a local vector. Three fixtures follow the form of 0178. The example `strings` proves.

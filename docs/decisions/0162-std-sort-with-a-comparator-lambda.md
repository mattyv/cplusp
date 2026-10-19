# 0162: std::sort with a comparator lambda. Slice three of 0160

Date: 2026-10-19. Status: decided. Amends 0161. This is slice three of 0160.

## Decision

- `std::sort(v.begin(), v.end(), [captures](T a, T b) { return e; })` sorts the whole of `v` with the comparator. `v` is a vector of integers of 0161. Each parameter of the lambda has the element type, by value or by `const&`. The lambda has the form of 0149: captures by copy, one `return`, and no call in `e`.
- The model writes `v := StdSort(v, (a: T, b: T) => e);`. Dafny proves `StrictWeakOrder` of the comparator at the call, from the text of `e`. A failure has the sentence `the comparator may not be a strict weak order.` A comparator such as `a.key < b.key` meets it, and `a <= b` does not.
- The core takes a comparator on a vector of a struct too, such as `a.key < b.key`. The vectors of a struct come in slice four: a local, a vector by reference and a return value.
- Any other comparator stays refused with the sentence of 0161. Examples are a named function, a functor, a lambda with a parameter of another type, and a lambda with more than one statement.
- The sentence of the failure names the comparator, not the call. A bot can then change the lambda.

## Why

C++ gives undefined behaviour for a comparator that is not a strict weak order, decision 0160. The model requires the order, so Dafny proves it for each comparator that the code holds. The lambda of 0149 is a test with no call, so Dafny can read its text in the proof.

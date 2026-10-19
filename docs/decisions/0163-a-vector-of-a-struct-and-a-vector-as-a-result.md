# 0163: A vector of a struct, and a vector as a result. Slice four of 0160

Date: 2026-10-19. Status: decided. Amends 0064, 0145 and 0160. This is slice four of 0160.

## Decision

- A vector of a struct of the file is a sequence of that datatype, as a vector of integers is. It can be a read-only parameter of 0064, a vector by reference of 0145, or a local copy of 0160. The struct must not hold a sequence, decision 0076.
- A function can give a `std::vector<T>` by value. The model writes the result as `seq<T>` with the bound of `Vec`, and a contract reads `result.size()` and `result[i]`. A `return` of a local vector gives its value. A `std::span` stays no result, because it is a view.
- A local vector can take the value of a call that gives a vector: `std::vector<T> x = f(a);`. The model writes `var x := f(a);`.
- The comparator lambda of 0162 on a vector of a struct, such as `a.key < b.key`, now reaches the model.
- A contract has no `multiset`. A contract that needs one names a predicate of the companion file, decision 0148. The example `sort_with_comparator` does so with `SameItems`, and the lemma `SmallestKey` gives the smallest key to its caller.

## Why

The example `sort_with_comparator` sorts a copy of a vector of a struct by one field, and gives the copy back. A caller reads the first element. Each piece is a value of C++, so the model of a sequence holds. The decisions 0160 to 0162 already cover the sort and the copy.

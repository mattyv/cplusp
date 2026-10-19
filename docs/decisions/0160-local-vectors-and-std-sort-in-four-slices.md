# 0160: Local vectors and std::sort, in four slices. Slice one: a local vector is a copy

Date: 2026-10-19. Status: decided. Amends 0064. The user asked the reviewer to choose how `std::sort` enters the model, and accepted its choice on 2026-10-19.

## The plan

The examples `algorithms` and `sort_with_comparator` need a local vector and `std::sort`. They come in four slices, in this order. Each slice has its own decision when it lands, and this file gives the shape of all four.

1. A local vector is a copy of a vector in scope. This decision makes slice one.
2. `std::sort(x.begin(), x.end())` on integer elements, with the default `<`.
3. `std::sort` with a comparator lambda of the form of 0149. Dafny proves that the comparator is a strict weak order at each call. A failure has the sentence `the comparator may not be a strict weak order.`
4. A vector of a struct as a local and as a return value. Also a local from a call that gives a vector.

The model of the sort is one Dafny `method StdSort(v, cmp)` in `divergence/dafny/Algorithm.dfy`. It requires `StrictWeakOrder(cmp)`. It ensures that the result has the same multiset of elements and the same length. It also ensures that no later element compares less than an earlier one. Its body is an insertion sort, so Dafny shows that a sort can meet the contract for each input that it allows. Callers see only the contract. The contract is the trusted part. C++23 [sort] and [alg.sorting.general] give it, and `prove` names it on this line:

```
Axiom: Algorithm.dfy: StdSort: std::sort with a strict weak order gives a permutation of its range, and no later element compares less than an earlier one, C++23 [sort] and [alg.sorting.general].
```

The requirement on the comparator is necessary. A comparator that is not a strict weak order gives undefined behaviour in C++. With no requirement, the model can also prove `false` after the call. The review showed this with `(a, b) => true`. A sort of doubles stays refused, because `<` on doubles is not a strict weak order with NaN. A sort of any other form also stays refused, with a sentence that names `std::sort`.

## Decision for slice one

- A local `std::vector<T> x = v;`, with `T` an integer type, is a copy. `v` is a sequence in scope: a parameter of 0064 or 0145, or another local vector. The model writes `var x: seq<T> := v;`. A later write to `v` does not change `x`, and a write to `x` does not change `v`. That is the value of C++.
- The function reads `x.size()` and `x[i]` as for a parameter. It writes `x[i] = e` and `x.push_back(e)` with the forms of 0145 and 0148: `x := x[i := e]` and `x := x + [e]`.
- A local `std::span` is a view of another sequence, not a copy. A write to the other sequence changes what the view reads, so it stays refused, decision 0064.
- These have no rule yet: a local vector with no initial value, and a local from a call or from a list of values. Also a local vector of a struct or of bool, and a call that passes a local vector by reference. The plugin sends a local vector with its own type, so the core never takes a view for a copy.

## Why

The reviewer weighed four options. A local vector trusts nothing new, so it comes first. An axiom for `std::sort` with no requirement on the comparator can prove a false fact. A verified body for the contract does not trust less of `std::sort`. But Dafny then checks that a sort can meet the contract. So a mistake in the contract cannot make the model prove `false`.

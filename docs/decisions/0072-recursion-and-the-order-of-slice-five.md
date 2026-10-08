# 0072: Recursion with a decreases line on the function, and the order of the fifth slice

Date: 2026-10-08. Status: decided. Amends 0061 on where a `decreases` line goes, and 0064 on the fifth slice.

## Decision

- A `//@ decreases` line above a function is the measure of its recursion. It reads the parameters, as a `requires` line does, and it cannot name `result`. Dafny proves that each recursive call makes the measure smaller.
- A recursive call is a call as 0058 says. A function may call itself, and two functions may call each other.
- Dafny proves that a recursion ends. It does not prove that the stack holds the depth. The contract must bound the depth, as in `examples/recursion`.
- `prove` names a recursive call whose measure may not get smaller: `the decreases line may not decrease at this call.`
- The fifth slice goes in this order, each step proved before the next. Recursion comes first, then structs of scalars, then `std::optional`, then structs that hold sequences, and recursive structs. Contracts that need specification functions, such as `Count` or `Wellformed`, wait for a decision on where those functions come from.

## Why

`radix_find` and `examples/recursion` recurse. Decision 0071 asks for small increments, and a test of a hard operation early. Recursion is small and needs no new data. The specification functions are the hard part, and they need a choice first.

## What changes

The core reads a `decreases` line above a function into the method. The shell prints it and names the new failure. An `invariant` above a function stays in the wrong place.

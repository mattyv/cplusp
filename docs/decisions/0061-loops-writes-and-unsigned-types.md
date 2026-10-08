# 0061: The third slice: loops, writes to locals, and unsigned types

Date: 2026-10-08. Status: decided. Amends 0057 on the third slice. Structs, `std::vector` and `std::span` move to the fourth.

## Decision

- `uint32_t` and `uint64_t`, and so `size_t`, are types of the subset. They map to Dafny newtypes with their ranges. The model never wraps, as 0058 says for casts. So Dafny proves that each step of unsigned arithmetic stays in range, and code that relies on the wrap does not prove.
- A literal in code prints with its type, such as `(1 as int32)`. Without the type, Dafny reads a literal that no context types as an exact integer. Then `2147483647 + 1 > 0` proved true, where C++ overflows.
- An assignment `x = e;` writes a local. Its value follows the rules of a start value, so a call that stands alone is allowed. A write to a parameter has no rule: Dafny parameters do not change.
- `++x` and `--x` as statements, and `x++` and `x--`, add or take one from a local. Dafny proves that the result fits the type. A compound assignment such as `+=` has no rule yet, because C++ promotes its operands first.
- A `while` loop is a Dafny `while`. A `for` loop with one local in its start, a condition and a step is the start, then a `while` whose body ends with the step. `break`, `continue` and any other `for` have no rule yet.
- The `//@ invariant` and `//@ decreases` lines directly above a loop belong to that loop. Each is a contract expression on exact integers, as 0057 says. A name in it is a parameter or a local of the function. Each name is declared once in a function, decision 0058, so the core finds it in one flat list. `result` has no place in a loop contract.
- A contract line in the wrong place is refused. `requires` and `ensures` go above a function, and `invariant` and `decreases` go above a loop.

## Why

Each loop in the examples and in `radix_find` counts with a `size_t`. A loop needs writes, and a loop proof needs an invariant. The flat list of names is enough because 0058 refuses a second declaration. A name that is out of scope at the loop makes Dafny refuse the file, so it fails loud.

## What changes

The core gains the two types, typed literals, assignments, steps, loops, loop contracts, and their rules in the proofs. The plugin writes loops, assignments and steps, and it claims the contract lines above a loop. The shell prints the loop and its contract.

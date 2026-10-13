# 0143: A range-for is a loop over indexes, and an index line names the index

Date: 2026-10-13. Status: decided. The user chose this form in October, with the draft that was then numbered 0113. Amends 0064 and 0110.

## Decision

- A range-for over a sequence parameter is in the subset: `for (T x : v)` or `for (const T& x : v)`. `v` is a parameter that is a span, a const vector or a const std::array. `T` is the element type of `v`, or `auto`. Its model is a loop over the indexes of `v`. The index is a `size_t` that starts at 0 and stops at `v.size()`. Each turn starts with `x` equal to `v[index]`.
- The line `//@ index i` above the loop names the index. The invariant and decreases lines of the loop, and the assert and apply lines in its body, can then read `i`. The name must be new in the function.
- Without an index line, the translator names the index itself, and no line can read it.
- The core adds the invariant `i <= v.size()` and the decreases line `v.size() - i`. The author writes neither.
- The core builds the loop. The plugin gives the core the loop variable, its type, the sequence, the contract lines and the body. The shell gives the core a new name for an index that has no index line.
- The core refuses an index line above any other loop or above a function. It refuses an index name that the function already has. The shell refuses an index line with more than one name, as a form it cannot read.
- A range over anything other than a sequence parameter, such as a field, a temporary or a local, has no rule yet. A loop variable that is a reference with no const has no rule.
- `break` in a range-for has the rule of `break` in a for loop.
- The sentence for a contract line in the wrong place changes. It becomes: `a contract line in the wrong place. A requires, an ensures, a modifies or a decreases line goes above a function. An invariant or a decreases line goes above a loop, and an index line above a range-for.`
- A new sentence names an index that is not new: `NAME on the index line is a name the function already has.`

## Why

A range-for is the loop that a C++ programmer and a bot write first. The examples `iterators` and `observer` use one. The gate already keeps the body from a change to the range, row range_for_mutation. The range is a const sequence, decision 0040. So the model of the loop is exact. An invariant of the loop needs the count of the elements before the current one, and C++ gives that count no name. The index line gives it one, in the same words as the invariant of a loop with an index.

The core builds the loop, and the shell does not. The loop is a rule of the translator, and the rules live in the core.

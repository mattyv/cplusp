# 0185: A vector that the code gives up

Date: 2026-10-24. Status: decided. Builds on 0145, 0160, 0171 and 0179. The example `rvalue_references` gives a vector to a function by rvalue reference, and the function moves it into a local.

## Decision

A parameter `std::vector<T>&&` is a reference parameter, as `std::vector<T>&` is, decision 0145. The two are the same here. The function lists the parameter on the `modifies` line, as 0145 says. `std::move(v)` of a vector, as the argument of such a parameter, passes `v` by reference, as for a struct, decision 0179.

`std::vector<T> w = std::move(v);` gives `w` the value of `v`. Here `v` is a local vector or a vector parameter by reference. After the move, `v` has any value, because C++ leaves a moved-from vector valid but unspecified. The gate refuses a read of `v` after the move, decision 0171. A parameter that a function moves from is a write, so the function lists it on the `modifies` line.

A local `std::vector<T> v(n, x);` is a vector of `n` copies of `x`. The count `n` and the value `x` each run once. C++ does not fix the order of `n` and `x`, so the rules of 0177 apply. `v(n, x)` throws when `n` is past `max_size()`, and the proof covers each return, as 0148 says. `v(n)` and `v{a, b}` keep the refusal of 0160. A brace list holds values, not a count and a value. `std::vector<bool>` keeps its refusal. A vector of `n` copies in any other place keeps the sentence of today.

A vector parameter by value keeps its refusal. A move of a vector in a `return`, in an assignment, or at a `const` reference parameter keeps the sentence of today. That is the sentence for a node with no rule.

## Why

An rvalue reference says that the caller gives the vector up. The callee takes its elements and leaves it empty, or in any state. The model cannot know that state, so it says nothing about it. Then no contract can rely on it. A vector of `n` copies is the common way to start a vector of a known size.

## What changes

The core reads a move into a local vector as the value of the source, then the source with any value. It reads `v(n, x)` as a sequence of `n` copies. The plugin writes `std::vector<T>&&` as a vector reference parameter, `std::move(v)` of a vector at such a parameter as `v`, and `v(n, x)` as its count and value. The shell prints the new forms. The example `rvalue_references` lists `v` on the `modifies` line of `consume`. Three fixtures follow the form of 0178. A fourth fixture reads a moved vector under a team policy that loosens `rvalue_references`, to show that the model keeps no value for it. A fifth checks the order rule in `v(n, x)`. The example `rvalue_references` proves.

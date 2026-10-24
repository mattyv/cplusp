# 0181: A temporary bound to a const reference

Date: 2026-10-24. Status: decided. Builds on 0094, 0178, 0179 and 0180. The example `callbacks` passes `Halve{}` and `CapAt{limit}` to a `const F&` parameter.

## Decision

A temporary of a plain struct with no destructor, bound to a `const T&` parameter, is its value. The model already reads a `const T&` parameter of such a struct as its value. The temporary is a new object, so no other name can see it or change it. It lives to the end of the full expression, and the callee only reads it.

The temporary can be a brace list, as `Pair{1, 2}`, or a call of a constructor, as `Cell(4)`. It can also be the value of a call that gives the struct. It can be the argument of a function, a member function or a constructor. A call of `operator()` and a call through a `unique_ptr` keep the refusal. A temporary of a class over an interface, at a parameter of the interface, keeps the refusal too. A destructor `= default` is no destructor here, decision 0179.

A temporary in the `return` of a function that returns a reference has no rule, at the line of the `return`. The temporary dies at the end of the `return`, so the caller gets a reference to a dead object. The sentence is "a temporary in the return of a function that returns a reference: the translator has no rule for it yet."

A temporary of a struct with a destructor keeps the refusal of 0178. A `const T&` parameter of such a struct has no rule, at the line of the function.

## Why

C++ binds the temporary to the reference and destroys it at the end of the full expression. A plain struct with no destructor does nothing when it dies. So the call sees the same value as a call with a named local, and the model has the words for that.

## What changes

The plugin writes a temporary of a plain struct with no destructor, bound to a `const T&` parameter, as its value. The core needs no change. Three fixtures: one that proves, one with a false claim, and one with a temporary in a return by reference. The example `callbacks` proves.

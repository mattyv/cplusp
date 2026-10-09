# 0095: The arguments of a member function in a contract, and what makes it pure

Date: 2026-10-09. Status: decided. Amends 0090, from the review of its green step.

## Decision

- A contract reads each integer as an exact integer, decision 0060, and a pure member function takes the integer types of C++. So each argument of a call of a pure member function in a contract passes as `(e as T)`, where `T` is the type of its parameter. Dafny proves that the value fits `T`, as the conversion of C++ requires.
- A member function is pure only when its contract also has a model. A member whose contract is refused has no Dafny function, so a contract that calls it is refused at its line with `NotPure`.
- A name that two `const` member functions of one struct share is left out of the members of the struct. A contract that calls it is refused with `NotPure`, so it never calls the wrong overload.
- Dafny can fail to prove a requires line of a member function at a contract that calls it. Then `prove` says "a requires line of the member function may not hold here." at the contract line. The line of the requires follows, as for a method of 0068.

## Why

The review found that `c.le(k)` with a parameter `k` reached Dafny as a type error. It also found that a member with a refused contract stayed pure. Its callers then named a function that the model did not print. And the rule for overloads was in the plugin and in no decision.

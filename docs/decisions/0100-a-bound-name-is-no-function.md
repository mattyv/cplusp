# 0100: A bound name is no function

Date: 2026-10-09. Status: decided. Amends 0098, from the review of its green step.

## Decision

- A name that a `forall` or an `exists` binds is an integer, decision 0064. A call of that name in a contract has no meaning, and the translator refuses the line. This is also true when a functor, a member function or a function of the companion file has the same name.

## Why

The review found that `forall c :: 0 <= c < 1 ==> c(x) == x` with a functor parameter `c` passed the translator. The core read `c` as the bound integer, so it did not call the functor. It then gave a call of a companion function `c` that does not exist, and only Dafny refused it. The review also found that the functor in `model-cond.cpp` gives the same value when it is called twice. So that file could not tell `f(f(x))` from `f(x)`, and it now also has a functor that adds one.

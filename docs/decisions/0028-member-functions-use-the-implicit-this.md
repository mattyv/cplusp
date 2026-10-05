# 0028: A member function's contract uses the implicit `this`, and the invariant is a predicate method

Date: 2026-10-05. Status: decided. Extends 0011, which made members implicit state.

## Decision

A member function's contract is written like any other: `requires`, `ensures`, `old(x)`, with the members in scope by name. There is no class-level clause. A non-const method may change any member, and a const method changes none, so members are never listed in `modifies` or `reads`. Only globals and statics are listed, as 0011 says. The class invariant is a const member function the bot writes, `bool valid() const` or a name of its own, and every public method says `requires valid()` and `ensures valid()`. The constructor ensures it.

In the model, one Dafny class per C++ class, and one per type for a class template. The fields are `var`s, the invariant is a predicate with `reads this`, and a method that changes a field has `modifies this`. A const method that computes from members only is a Dafny `function` with `reads this`. An owned object, as behind a `unique_ptr` member, is in the frame through Dafny's `Repr` idiom, on the Dafny side.

## Why

Dafny has no class invariant. Its idiom is a predicate `Valid()` that every method requires and ensures. VeriFast does the same with a separation-logic predicate, and Verus with `self.valid()` and `old(self)`. With the implicit `this` and a predicate method, the C++ contract and the prover's contract are the same text, clause for clause. The match check that ties them is then a comparison. A class-level clause would make the trusted tool expand the invariant into every method, and know when not to, once per prover. C++26 contracts have `pre` and `post` and nothing at class level, so the clauses map onto them one for one. The repetition is honest: a reader of one method sees what it needs on that method. A class-level clause can come later as sugar that expands to these lines.

## What changes

The examples: a member function names no member in `modifies` or `reads`, and a class with an invariant has a predicate method the contracts name. examples/README.md states the convention. The match check, when it comes, ties class to class, field to field, and the predicate to the predicate.

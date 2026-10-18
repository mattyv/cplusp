# 0157: A count_if with no rule names the limit that it misses

Date: 2026-10-18. Status: decided. Amends 0149 and 0155.

## Decision

- A call of `std::count_if` that misses the rule of 0149 is refused with a sentence that names the limit. The sentences are these, each with `: the translator has no rule for it yet.` after it:
  - `count_if over a range other than v.begin(), v.end() of one sequence parameter`
  - `count_if with a function or a functor in place of a lambda written in the call`
  - `count_if with a lambda whose parameter is not the element type`
  - `count_if with an init capture in its lambda`
  - `count_if with a lambda whose body is more than one return`
- The plugin gives the first limit that the call misses, in the order of the list, and no other line for the call.
- A miss that fits none of the five keeps the sentence of a call with no model. Examples are an execution policy, a body that is not of type `bool`, and a lambda that the gate refuses. A lambda with two parameters gets the sentence of the parameter.

## Why

Before this, every miss gave `a call to std::count_if<...>, which has no model in view.` The bot had to guess which limit of 0149 it missed. The review of 0149 asked for the limit by name.

# 0033: One root, one writer

Date: 2026-10-05. Status: decided, after the gate held it and two reviews read it. Amends the aliasing rule of 0029, which made `requires &a != &b` a contract clause. Follows a third outside review.

## Decision

Every argument of a call that binds to a reference, a pointer or a span has a root. So does the object of a member call. The root is the named object the expression reaches. That is a local, a parameter, `this` with a path of members under it, or a global. The expression reaches it through member access, a subscript, or the dereference of a `unique_ptr` or an `optional`. It also reaches it through `subspan`, `first`, `last`, a cast or parentheses. The loop variable of a range-for by reference has the root of its range. A temporary has a fresh root.

When one of those arguments can write, every root in the call is disjoint from every other. Two roots are disjoint when neither is the other, and neither is a subobject of the other. An argument can write when it binds to a non-const reference, a non-const pointer or a span of non-const elements. The object of a non-const member call can write too. The gate refuses a call that breaks this under the row `aliasing`. A global or a static is never an argument to a reference, a pointer or a span, because it is the State as well. The clause `requires &a != &b` leaves every contract. The gate holds the fact at every call, and a value has no address.

The gate refuses a write through a const handle too, under the row `unique_ptr`. A write is an assignment, an increment, a non-const member call, or a binding to a non-const reference, pointer or span. The check follows the path to the root, and a step through the dereference of a const `unique_ptr` makes the path const.

Beside an unordered change of state, an operand may be a literal, or a local or a parameter whose root the change does not write. A call, a global or a member of an object the change writes may not stand there. The row `evaluation_order` carries this.

## Why

The review showed that 0029 closed one alias and left the others. A non-const and a const reference to one object, `f(x, x)`, returned 1 where the model said 0. A reference to a struct and one to its member differ in type and overlap in storage. A const vector and a non-const one, `g(v, v)`, gave a use after free. The clause `requires &a != &b` had no meaning in the model, because a value has no address, so nothing ever proved it. The review also showed `*p = 42` through a const `unique_ptr`, and `before(next(x), x)`, which clang and GCC answer differently. The value model is exact only when no two names in one call reach one object. The gate can hold that at every call site by looking at the arguments. The rule then holds in every verified function, by induction over its callers.

Three ceilings stay. The gate does not run on a plain function that calls verified code, so that call may alias. A human reviews it as part of the trusted boundary. The gate refuses two spans cut from one buffer in one call, even where the cuts do not overlap. The upgrade is a rule for `first(n)` beside `subspan(n)`. The gate refuses a call beside another call until it reads `reads` and `modifies` from the contract, gap 4. Until then any call may touch the State.

## What changes

The row `aliasing` with the check `cplusp-aliasing` and a sample pair. The row `unique_ptr` moves from a matcher to the check `cplusp-const-handle`. The row `evaluation_order` gains the read rule and three banned lines. The battery case `reference_aliasing` moves to the gate side, and the case `const_alias` joins it. Every `requires &a != &b` leaves the examples, the pairs and the skill.

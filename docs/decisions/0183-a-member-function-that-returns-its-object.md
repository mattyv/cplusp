# 0183: A member function that returns its object

Date: 2026-10-24. Status: decided. Builds on 0094, 0178, 0179 and 0182. Amends 0096 on a function that returns a reference, and 0177 on a call that gives no value. The example `builder` chains steps that each set a field and return the builder.

## Decision

A member function that writes its object can return `T&` of its own class when its body ends in `return *this;` and each of its `return` statements is `return *this;`. The translator reads it as a member function that writes its object and gives no value, decision 0096. Its result is the object itself. The plugin checks each `return` of the body, so the contract need not say so. A contract cannot name `&result`.

A chain `x.f(a).g(b)` calls `f` on `x`, then `g` on `x`, in that order. C++ evaluates the object of a call before the call, so this is the order of the standard. The arguments of a step run after the step before it, and before the step itself. A step has the line of the statement of its chain.

The chain can stand as a statement. It can also be the object of a last call that gives a value. That last call must be the full value of a `return`, or the full start value of a local. An example is `return x.f(a).total()`.

A chain in any other place keeps the refusal of 0104 and 0177. These places are:

- an operand or an argument,
- the condition of an `if`, a `while` or a `for`,
- a branch of `?:`, and the right side of `&&` or `||`.

So the steps of a chain never go to a place where the core cannot see the order. The sentence is "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone."

The object of a chain can be a local, a reference parameter or a temporary. A temporary gets a fresh local, as the values of an init list do, decision 0179. A temporary of a struct with a destructor keeps the refusal of 0178. A chain on `this`, on a field or on a global keeps the refusal of a write back to it. A member function that returns `const T&` keeps the refusal of `*this` in its `return`. A chain in the head of a `for`, as its start or its step, has no rule. The sentence is "a chain of calls in the head of a for: the translator has no rule for it yet."

These forms have no rule:

- a member function that returns `T&`, at the line of the function, when its body does not end in `return *this;`. The same holds when one of its returns is not `return *this;`. The sentence is "a reference result that is not `*this`: the translator has no rule for it yet."
- the result of such a call used as a value, at the line of the statement. Examples are the argument of a call and the value of a `return`. The sentence is "the result of a call that gives back its object, used as a value: the translator has no rule for it yet."

## Why

A fluent builder is a common form, and the gate already takes it. Each step writes the object and hands the same object to the next step. The model already has a member function that writes its object. The chain is only a list of such calls on one object.

## What changes

The plugin writes such a member function as one that gives no value, and a `return *this;` as `return;`. It writes a chain as one call on the object for each step, in order, with a fresh local for a temporary. The core refuses a call that gives no value inside an expression as a call out of place, after the refusals of its arguments. Before, it gave the sentence of a contract line. The core test `a_call_that_gives_no_value_inside_an_expression_is_out_of_place` holds it. The example `builder` drops `&result == this` from its contracts, and the open forms of `docs/soundness.md` drop it too. The comment of `examples/builder/example.dfy` changes to match. Three fixtures follow the form of 0178. The example `builder` proves.

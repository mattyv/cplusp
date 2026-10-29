# 0214: The object as an argument

Date: 2026-10-29. Status: decided. Builds on 0089, 0096 and 0166. The example `visitor` has `v.visit(*this)` in `Square::accept`. The translator refuses it with `UnaryOperator *: the translator has no rule for it yet.`

## Decision

In a member function, `*this` is the object of the member function, as `this->f` reads it, decision 0166. It can be the argument for a parameter by value or by `const&`. The callee then reads the value of the object at the call.

`*this` as the argument for a reference that is not `const` has no rule yet. The sentence is ``*this` as a reference that is not const: the translator has no rule for it yet.``

## Why

A const reference and a value are values in the model, decision 0029. So the object as such an argument is its value, and the callee cannot change it. The visitor pattern passes the element to the visitor in this way. A reference that is not `const` would be a second name for the object while the member function writes it. The model has no such alias.

## What changes

The plugin writes `*this` as the object. Three fixtures follow the form of 0178.

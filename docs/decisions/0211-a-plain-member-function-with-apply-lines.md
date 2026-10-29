# 0211: A plain member function with apply lines

Date: 2026-10-29. Status: decided. Amends 0189. The example `type_erasure` has `int32_t area() const { return side * side; }` in a struct. The bound of the product needs an apply line of 0167. With the line, the body has two statements, so the member function is no plain member function, decision 0189. Then `Model<T>::area()`, which calls it, has no function in the model.

## Decision

A plain member function of 0189 can have apply lines above its `return`. Each apply line calls a lemma of 0099 or 0167. The function of the member function is `L(a); e`, as 0167 says.

## Why

An apply line calls a lemma, not a function. A lemma adds a fact and changes no value. So the order on the functions of 0189 holds: a plain member function still calls no function. The bound of a product needs the line, and a small accessor that multiplies two fields is common.

## What changes

The core reads a body of apply lines and one `return` as a plain body. Two fixtures follow: one proves, and one holds a false claim.

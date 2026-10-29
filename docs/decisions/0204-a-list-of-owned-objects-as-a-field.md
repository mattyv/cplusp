# 0204: A list of owned objects as a field

Date: 2026-10-29. Status: decided. Builds on 0165, 0168, 0170, 0187 and 0191. The example `observer` keeps its observers in a field `std::vector<std::unique_ptr<Observer>>`. The model reads such a vector as a parameter already, decision 0170, but not as a field.

## Decision

- A class can have a field `std::vector<std::unique_ptr<T>>`, where `T` is an interface of 0165 or a struct of 0073. The model gives it the type of 0170, a sequence of `Option`. The field starts empty when the init list does not name it, as 0187 says.
- In a member function, `f[i]->g(a)` calls `g` on the element, as on a parameter of 0170. A `const` call reads the element. A call that is not `const` writes the element back, and Dafny checks that the index is in range and that the element is not null.
- `v.push_back(std::move(o))` adds the value of the `std::unique_ptr` local or parameter `o` at the end of the vector `v`. Then `o` is null, decision 0171. `v` can be a field, a local or a reference parameter.

## Why

A list of owned objects behind an interface is the common form of a container of polymorphic values in C++, and the gate passes it. The model of 0170 already holds the right shape for a parameter. The field and the move into the vector close the gap with the same shape.

## What changes

The plugin accepts the field and the argument `std::move(o)` of `push_back`. The core gives the field the type of 0170 and writes the move as a push of the value with the null after it. Two fixtures show the forms: one proves, and one holds false claims.

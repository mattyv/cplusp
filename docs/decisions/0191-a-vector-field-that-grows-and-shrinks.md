# 0191: A vector field that grows and shrinks

Date: 2026-10-25. Status: decided. Builds on 0096, 0148, 0181, 0187 and 0188. The example `stack_template` keeps its items in a vector field, and adds and takes away the last one.

## Decision

In a member function that writes its object, `f.push_back(e)` adds `e` at the end of a vector field `f`, as 0148 says for a vector by reference. Dafny reads it as `this' := this'.(f := this'.f + [e]);`. A failed push_back throws and never returns to verified code, as 0148 says.

`f.pop_back()` takes away the last element of a vector field `f`. `f.back()` reads the last element of a vector, in code and in a contract. C++ gives undefined behaviour for either on an empty vector. So the prelude gains two functions with a body, `PopBack` and `Back`, each with the requires line `|s| > 0`. Dafny proves that line at each call. The sentence is `a requires line of the callee may not hold.` The C++ library says the same, because each of the two needs a vector that is not empty.

A `const` member function can give back `const T&` of a scalar or a plain struct `T`. Its `return` must be a field of its object, an element of a vector field as `f[i]` or `f.at(i)`, or `f.back()`. The model reads the result as a value of `T`. The gate refuses a reference local, under the row `lvalue_references`. So the code reads the value of the call at once, before any later write can change it.

A braced value of a plain struct, as `Point{1, 2}`, at a parameter `const T&`, is its value. This is the rule of 0181 for a temporary, and it holds for each instance of a class template too.

These have no rule yet, and keep the sentence of today:

- `pop_back` of a vector that is no field of the object,
- `front()`, `emplace_back` and `insert` of a vector,
- a `const T&` result whose `return` is any other expression, as a parameter.

## Why

A stack is the first container that most code builds on a vector. Its member functions add and take away the last element, and give back a reference to it. The model already has the value of a vector field, decision 0187. Each of these operations is a new value of that field, or a read of it. The two functions of the prelude carry the requires line of the C++ library, so the prover checks each call.

## What changes

The core reads `push_back` and `pop_back` of a vector field, and `back()` of a vector. The plugin writes them, the `const T&` result as a value, and the braced value at a `const T&` parameter. The shell prints the two functions of the prelude. Three fixtures follow the form of 0178. The example `stack_template` gets an explicit instantiation for each instance, as 0188 says, and proves.

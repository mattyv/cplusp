# 0194: A vector by value

Date: 2026-10-27. Status: decided. Builds on 0145, 0160, 0185 and 0186. Reverses the sentence of 0185 that a vector parameter by value keeps its refusal. The example `custom_range` gives a vector to a constructor by value, and the constructor moves it into a field.

## Decision

A parameter `std::vector<T>` by value is a copy that the function owns. The model reads it as a local vector of the body that starts with the value of the argument, decision 0160. So the body can read it, write its elements, add to it with `push_back` and move it, as it can for a local vector. The caller never sees these writes. A contract line reads the parameter as the value that the caller gave.

`std::move(v)` can be the argument of a parameter by value. Here `v` is a local vector or a vector parameter by value. The argument gets the value of `v`. After the call, `v` has any value, as 0185 says for a move into a local. The same holds in the init list of a constructor, as `items_(std::move(items))`.

A copy of a vector, as the argument of a parameter by value, gives the argument the value. The source keeps its value.

A function with a vector parameter by value is never a pure function, decision 0090. Its body is a block of the local vector, not one `return`. So a contract cannot call it. A vector by value of a type with no rule keeps the sentence of today, as for a local vector.

## Why

A constructor that takes its data by value and moves it into a field is the common form of C++ since 2011. The caller can give a copy or give the vector up, and the constructor holds one way for both. The model already has a local vector, a move into a local, and a parameter that becomes a local of the body, decision 0186. A vector by value is the same: a local that starts with the value of the argument.

## What changes

The core reads a vector parameter by value as a local of the body. It reads a move of a vector at a parameter by value as the value, then the source with any value. The plugin writes a vector parameter by value, and `std::move(v)` of a vector at such a parameter. The shell needs no change. The fixture of 0185 that refused a vector by value now proves at that line. Three fixtures follow the form of 0178. A fourth reads a vector after its move under the team policy of 0185, to show that the model keeps no value for it. The example `custom_range` proves.

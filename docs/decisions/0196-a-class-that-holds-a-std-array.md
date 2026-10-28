# 0196: A class that holds a std::array

Date: 2026-10-28. Status: decided. Builds on 0132, 0184 and 0187. Amends 0132 on an array in a field. The example `small_vector` keeps its elements in a `std::array` field.

## Decision

A field `std::array<T, N>` of a scalar `T` is a sequence of length `N`. The model gives it a Dafny type that holds the length, `Arr'N<T>`, which is a `seq<T>` whose length is `N`. So each object of the class has an array of length `N`, and Dafny proves that each write keeps the length. A read `f[i]`, `f.at(i)` and `f.size()` is as for a vector field, decision 0187, in code and in a contract. A member function that writes its object can write `f[i] = e`, and Dafny proves the index.

The field gets its start value in the init list, as `f()` or `f{}`, or from a default member initializer `{}`. Each gives `N` zeros, as C++ does for a value-initialized array of scalars. A field that gets no start value has no rule, at the line of the constructor. C++ leaves its elements without a value. The sentence is `a std::array field with no start value: the translator has no rule for it yet.`

These keep the sentence of today:

- a `std::array` field of `bool`, of a struct, or of a pointer,
- a start value of the field as a brace list of values,
- a write of the whole field.

## Why

A small container with no allocation keeps its slots in a `std::array` and counts the ones in use. The model has a fixed array as a local, decision 0184, and a sequence as a field, decision 0187. A field needs one more fact: its length holds in each object, also in one that a caller made. A type that holds the length gives that fact to each function with no contract line.

## What changes

The core gives a `std::array` field of a scalar the type `Arr'N<T>`. It reads `N` copies of a value as the start value of a local array of length `N`. The plugin writes the field and its start value. The shell prints the type and declares it once for each length. The fixture of 0132 that refused an array field now proves at that line. Three fixtures follow the form of 0178. The example `small_vector` proves.

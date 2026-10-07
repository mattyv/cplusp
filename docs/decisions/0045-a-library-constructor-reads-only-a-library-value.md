# 0045: A library constructor reads only a value of the library

Date: 2026-10-07. Status: decided. Amends 0044, which let a library constructor read a value of a type argument.

## Decision

A constructor of the library reads an argument only when the argument is a number or a type of the library. The argument must also be the type built or one of its type arguments. A type of the file takes its copy through its own constructor, which is code of the file. So `std::optional<W> o(*p)` through a const handle is no read when `W` is a type of the file. `std::optional<W> o(std::as_const(*p))` is the way.

## Why

`std::optional<W>` forwards a non-const `W&` to the constructors of `W`. A `W(W&)` that the file writes may change its argument, and the eighth review found one that did, in a file the gate passed. What runs counts, decision 0038. A copy constructor of the file runs.

## What changes

The constructor rule of 0044 asks also that the argument is not a record of the file. A fixture with such a `W`.

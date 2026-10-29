# 0216: A static and a member function of one name

Date: 2026-10-29. Status: decided. Amends 0095 and 0174. The review of 0215 found a contract call that proved with the wrong function. A class had a static member function `get` and a member function `get`. A contract line `s.get(x)` with an `int32_t` `x` read the member function, but C++ calls the static one.

## Decision

A static member function and a member function of one name are two functions of that name. So the name is an overload in both forms, `s.get(x)` and `S::get(x)`. A contract that calls it gets the sentence `get is no pure function. A contract calls a function with one return and no write.`

## Why

Decision 0095 says that a contract never calls the wrong overload. In C++, overload resolution reads a static member function and a member function of one name together. The plugin kept the two names apart, so each one looked like a name with one function.

## What changes

The plugin counts a static member function and a member function of one name under both names. One fixture holds the two forms.

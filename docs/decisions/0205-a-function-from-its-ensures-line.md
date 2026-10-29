# 0205: A function from its ensures line

Date: 2026-10-29. Status: decided. Builds on 0090, 0095 and 0189. The example `observer` has a member function `valid()` whose body is a loop. A contract calls `valid()`, and a function with a loop has no function in the model, decision 0090.

## Decision

Take a `const` member function that gives `bool`, whose body is no pure body. It has a function in the model when an ensures line of it is `result == e`. The function is `e`, with the requires lines of the member function. A contract can then call the member function, as one with a pure body, decision 0090.

The method still has its body and its contract. Dafny proves that the body gives `e`, so the function and the method agree.

This amends 0172, 0189, 0190 and 0194. Take a body that writes a local, holds a loop, or takes a vector by value. Or take a body that calls a member function that is no plain member function. Each is no pure body. Such a member function that gives `bool` now takes its function from its ensures line too. So the fixtures of 0172, 0189 and 0194 that test such a member function now give an integer from it. Their tests keep their lines.

The rule holds for the first such ensures line. A member function that writes its object, a static member function, a free function, a trusted function and a virtual function keep their rules.

## Why

An invariant of a class is often a loop over a field, and a contract reads the invariant in each line. The ensures line `result == e` already says the value of the function in the language of the contract, and Dafny proves the body against it. So `e` is a true function of the object, and the model can use it.

The ceiling is a result of `bool`. A result of an integer type needs a proof that `e` fits the type in the function, and the function has no body to show it. The upgrade path is a requires line or a range in the contract.

## What changes

The core gives such a member function the function `e`, in the strict marks of the table of members, decisions 0095 and 0190. Three fixtures follow the form of 0178.

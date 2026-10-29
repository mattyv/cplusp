# 0210: Two virtual functions of one name

Date: 2026-10-29. Status: decided. Amends 0165. The example `visitor` has `visit(const Square&)` and `visit(const Rect&)` in one interface. The translator refuses the interface with `Visitor has two virtual functions of one name. The translator has no rule for it yet.`

## Decision

Two or more virtual functions of an interface can share a name when their parameters differ. The plugin gives each one a name in the table of members that holds its parameter types. An override of `D` with the same name and parameter types gets the same name. The check of each override then finds it by that name, decision 0165, and code calls each one by its key, as C++ picks it.

A contract cannot call such a function by its name yet. The sentence is the one of a function with no function in the model, decision 0090.

## Why

C++ picks among functions of one name by the types of the arguments, and the visitor pattern depends on it. The plugin sees the choice that clang made in each call, so code needs no new rule. The check of an override is by name, so a name that holds the parameter types keeps each pair apart.

## What changes

The plugin names each such function, in the interface and in each class over it. The core needs no change. Three fixtures follow the form of 0178.

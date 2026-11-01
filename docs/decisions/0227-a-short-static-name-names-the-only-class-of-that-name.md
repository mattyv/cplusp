# 0227: A short static name names the only class of that name

Date: 2026-11-01. Status: decided. Amends 0226. The review of the fix for 0226 found a proof about the wrong function. A namespace `a` declares `T::up` with no body, and the file defines `::T::up`. A contract in `a` that calls `T::up` proved about `::T::up`, because the walk through the namespaces skipped `a`. The review also found that the check of a stored address of 0226 made `std::max(g_s.x, g_s.y)` a change of `g_s`.

## Decision

- A short name of a static member function, such as `T::up`, resolves only when the file has one class of the name `T`. Then it names the static member function `up` of that class, when the file gives it a body. In each other case the sentence is `T::up names no static member function from here. Write the full name.` A full name keeps its rules.
- The plugin writes no scope of a function for this rule.
- A pointer into a struct global, such as `&g_s.y`, is that global in the check of a stored address. When it is an argument of a call, the parameter of the call decides whether the global changes, as before 0226.

## Why

The lookup of C++ needs the scopes that the plugin sees and the shell does not. One class of the name gives one function, whatever the scope of the contract. The rule refuses more than C++ does. It never gives a proof about another function.

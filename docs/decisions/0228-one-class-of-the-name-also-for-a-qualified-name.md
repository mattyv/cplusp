# 0228: One class of the name, also for a qualified name

Date: 2026-11-01. Status: decided. Amends 0226 and 0227. The review of the fix for 0227 found three more cases.

## Decision

- The rule of 0227 holds also when the class part has `::`, such as `a::T::up`. The name resolves only when the file has one class whose name is `a::T` or ends with `::a::T`. Before, an exact match came first. So in a namespace `b` that has its own `a::T`, the name named `::a::T::up`, and C++ names `b::a::T::up`.
- A class that the file only declares counts as a class of its name.
- The check of a stored address reads a constant global of the file, as it reads a constant of the compiler. So the address of a state global in it counts. A call that writes through `const Holder g_h{&g_total}` changes `g_total`.

## Why

The first case is a proof about the wrong function. The second case gave a proof about a function that C++ does not find from the contract. The third case is a pass with no finding when a team loosens `raw_pointer`. The translator matches a short static name by the end of the class name, not by the lookup of C++. So a free function can write `T::up` for `Outer::T::up`.

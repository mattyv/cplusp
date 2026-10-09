# 0112: Only a reference parameter hides a global on a modifies line

Date: 2026-10-09. Status: decided. Amends 0111.

## Decision

A name on a modifies or reads line hides a global of the same name only when it names a reference parameter. That is a parameter of type `T&` that is not const. A parameter by value or by const reference hides nothing. The name then stays the global, as before 0111.

## Why

A modifies line can name only a reference parameter, decision 0108. A parameter by value is a copy, and the function cannot change the caller's value through it. The sample pair of global_state has a function with a parameter by value `total` and the line `modifies total`. Its body writes the global `::total`, and the gate refuses its caller, because the caller does not list `total`. That pair stays true with this rule. The coder found the case in the green step of 0111.

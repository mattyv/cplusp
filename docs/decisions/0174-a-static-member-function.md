# 0174: A static member function is a free function with the name of its class

Date: 2026-10-23. Status: proposed. Builds on 0090 and 0173. This is step two of the plan of 0173, for the examples `singleton` and `arena`.

## Decision

A static member function is a free function with the name of its class, `c_Tally'bump'`. Its globals are implicit parameters, decision 0173. A static member function with a `reads` line and no `modifies` line can get a function twin, `c_Tally'valid'(v_Tally'count_)`. The rule is the one for a const member, decision 0090. A contract calls the twin. A requires line gives it the values before, and an ensures line the values after.

## Why

The examples `singleton` and `arena` keep their data in static data members and read it through static member functions. Their contracts call those functions, such as `valid()` and `count()`.

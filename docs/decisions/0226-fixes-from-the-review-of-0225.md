# 0226: Fixes from the review of 0225

Date: 2026-11-01. Status: decided. Amends 0174 and 0225. The review of the green step of 0225 found these defects. Each has a fixture.

## Decision

- The address of a global that goes into an object changes the global, also through a value that is not a constant. Examples are a local pointer, a conditional, and the elements of a vector. 0225 said this, but the state check found only a constant address.
- A short name of a static member function, such as `T::up`, resolves only through the class of the member function whose contract holds it. A contract of a function in no class writes the full name. Another short name gets the sentence `T::up names no static member function from here. Write the name with its namespace.`
- The model leaves out a global of a struct that it leaves out. The global then gets the sentence of a global with no rule. Before, the run stopped with a panic, or Dafny printed a type error.
- An empty `DAFNY` is a `DAFNY` that is not set.

## Why

The first case is a pass with no finding. The second case is a proof about the wrong function. The short name matched a function of another namespace by the end of its name. The third case is a panic from a file of a few lines. The shell has no namespace of a function, so the class of the member function is the only scope it can trust.

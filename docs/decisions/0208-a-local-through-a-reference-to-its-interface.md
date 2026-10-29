# 0208: A local through a reference to its interface

Date: 2026-10-29. Status: decided. Builds on 0108, 0165, 0166 and 0169. The example `visitor` passes a local `AreaSum sum` to a parameter `Visitor& v`, and then reads `sum.seen()`. The translator refuses that argument with `a class as a reference to its interface: the translator has no rule for it yet.`

## Decision

A local `d` of a final class `D` can be the argument for a reference parameter `B&`, when `B` is an interface of `D`. The model passes the upcast of `d` to the call, decision 0166, and gets back the value `w` of the parameter after the call, decision 0108. Then it gives `d` a new value whose upcast is `w`.

Dafny cannot find that value from the model alone, so the model takes its existence as given. C++ says it: a call through a reference to `B` runs the overrides of `D`, so the object is still a `D` after the call, C++23 [class.virtual]. `prove` names this on one line for each such pair of `D` and `B`:

```
Axiom: model: D: a call through a reference to B leaves an object of D, C++23 [class.virtual].
```

A local of a class that is not final, a field, a parameter and a value in a vector have no rule yet for this. Each keeps the sentence above.

## Why

A visitor, a sink and a callback are each a local of a concrete class that a function changes through its interface. After the call, the caller reads the local through its own class. The upcast of 0166 goes from `D` to `B` only, so the model needs a way back. The new value of `d` is any `D` whose upcast is `w`. Each fact that the caller learns about `d` then comes from the contract of the call through `B`, and the upcast says that `B` reads `d` as `D` does.

The assumption is consistent. In C++ the object after the call is a `D` whose value meets the contract of the call, because Dafny proves the callee and each override. So some `D` has the upcast `w`.

## What changes

The plugin writes the argument as a change of the local into its interface, by the keys of `D` and `B`. The core writes the call with the upcast before it and the new value of the local after it. The shell prints the new value as `d :| f_D'B(d) == w` after an assume of its existence, and prints the Axiom line. Three fixtures follow the form of 0178.

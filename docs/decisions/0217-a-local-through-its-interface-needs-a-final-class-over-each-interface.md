# 0217: A local through its interface needs a final class over each interface

Date: 2026-10-29. Status: decided. Amends 0208, 0210 and 0214. The review of 0208 to 0214 found a wrong program that proved. A function passed a local `Total t` to `p.poke(t)`, a virtual function of an interface `Poker` with no class in the file. The contract of `poke` gave a value of `Sink` that no `Total` can have. So the assumption of 0208 was false, and each line after the call proved.

## Decision

- The core writes a local back through a reference to its interface, decision 0208, only under one condition. Each interface of the file must have a final class over it in the file. Otherwise the call keeps the sentence `a class as a reference to its interface: the translator has no rule for it yet.`
- `*this` for a reference that is not const has no rule in a member call or in a call of `operator()` either, decision 0214.
- A sentence names one of two virtual functions of one name by its plain name, decision 0210. A contract that calls such a name gets the sentence `size is no pure function. A contract calls a function with one return and no write.`
- A `const` and a non-`const` virtual function of one name are two overloads, decision 0210.
- The object of a call is never a local through its interface. The core has no rule for it.

## Why

0208 says that the assumption is consistent because Dafny proves the callee and each override. That holds only when each contract on the path of the call has an override that Dafny checks. A contract of an interface with no class in the file has no such check. It can hold for some value of `Sink` and for no value of `Total`. A final class over each interface gives a checked override for each virtual function. Each override meets its contract for each `Sink` that keeps the contract of `Sink`, so also for the `Total` of the call.

## What changes

The core gets the classes over each interface. When an interface has no final class, the core refuses each function that writes a local back through its interface. The plugin refuses `*this` in a member call and in a call of `operator()`. It gives a `const` virtual function a table name apart from the non-`const` one. The shell names a function of two overloads by its plain name in each sentence. Four fixtures hold the cases.

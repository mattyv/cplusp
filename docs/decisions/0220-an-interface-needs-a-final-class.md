# 0220: An interface needs a final class

Date: 2026-10-29. Status: decided. Amends 0165 and 0217. The review of 0217 found a wrong program that proved. The interface `Poker` had no class in the file, and its contract `result == 1 && result == 2` cannot hold. A function called `p.poke()` and then proved `result == 42` while it returned 0.

## Decision

Each interface with a virtual function in the file must have a final class over it in the file. When one has none, `prove` refuses it at the line of its first virtual function: `Poker has no final class over it in the file, so the translator cannot check its contract.`

## Why

The model takes the contract of each virtual function of an interface as an axiom, decision 0165. `prove` checks that axiom on each override in the file. With no override in the file, nothing checks it, and a contract that no override can keep makes each fact true. A final class over the interface gives an override that Dafny checks against each contract. Then the axiom holds for that class, so it cannot be false. The check of 0218 makes sure that the proof of each override ends, so no override proves its contract from the axiom itself. This rule also covers the case of 0217, but 0217 stays: it names the line of the call.

## What changes

The core lists each interface of the file with no final class over it among the refusals of the upcasts. It proves that such an interface always gives a refusal. The shell prints the sentence. One fixture holds the case.

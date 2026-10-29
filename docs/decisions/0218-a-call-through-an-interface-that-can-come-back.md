# 0218: A call through an interface that can come back

Date: 2026-10-29. Status: decided. Amends 0165, 0209, 0214 and 0217. The review of 0217 found a wrong program that proved. The override `Loop::fill` passed `*this` to `helper`, and `helper` called `f.fill(s)` through the interface `Filler`. In C++ this recursion never ends. In the model, a call through an interface is a method with a contract and no body, so Dafny sees no recursion. Dafny proved the contract of `Loop::fill`, which cannot hold, from the contract of `Filler::fill`. Then each caller got a false fact.

## Decision

The core makes the call graph of the file. A function has an edge to each function that its body calls, and to each destructor of the file. A call through a virtual function `B::f` also has an edge to each override of `B::f` in the file. A call through `B::f` in a function `g` has no rule when an override of `B::f` has a path to `g`. The sentence is `the call of Filler::fill can run Filler::fill again before it returns: the translator has no rule for it yet.`

The core takes the functions that a path from an override reaches, until no step adds a function. The count of the functions of the file and one more is the limit of the steps. When the steps do not end in that limit, the core takes it that the path reaches each function.

The walker of 0217 reads each statement of a Dafny body. Its proof says what it finds, not that it finds each place. A fixture holds a write-back through an interface in each place of a body.

## Why

The check of an override against its interface is sound only when the calls through the interface end. Dafny proves that a recursion of methods ends, but it cannot see a recursion that goes through an interface. The call graph makes each such recursion visible to the core. A recursion that does not go through an interface stays with Dafny, which checks its `decreases` lines. A visitor stays allowed. `accept` calls `visit` through the interface, but no override of `visit` calls `accept`.

## What changes

The core gets the call graph from the bodies of the functions and the overrides of the upcasts. It refuses a call through an interface that can come back. The shell prints the sentence. Four fixtures hold the cases.

# 0169: A virtual function that is not const. Slice three of 0165

Date: 2026-10-20. Status: decided. Amends 0096, 0108, 0142 and 0165. This is slice three of 0165. The reviewer checked the model in Dafny before the tests.

## Decision

- A pure virtual function that is not `const` is a method of the interface with no function and no upcast line. It takes its object in and gives it back, decision 0096, and its reference parameters stand on its modifies line, decision 0108. Dafny takes its contract as given.
- Its override is a member function of 0096, and its body proves its own contract. `prove` checks the override against `B::f` on the contracts. The requires lines of `B::f`, read on the override, must give the requires lines of the override. The ensures lines of the override must give each ensures line of `B::f`, read on the override. The sentences of 0165 stay.
- A parameter `B& b` of an interface on the modifies line takes a value of `B` in and gives it back. `b.f(a)` in code runs `B::f` on it.
- `p->f(a)` on a local `std::unique_ptr<B> p` writes the new value back to `p`. This amends 0142. A write through `const std::unique_ptr<B>&` is a finding of the gate. The translator refuses a write through `*p` or through any other place with the sentence of 0108.
- A `D` object at a `B&` parameter has no rule yet: `a class as a reference to its interface: the translator has no rule for it yet.` The model has no way back from a value of `B` to a value of `D`.
- The translator refuses an override whose method has no contract at its class: `the override of B::f in D has no method in the model, so the translator cannot check it.`
- `c.value()` in a contract on an object of a struct calls its member `value`, as `c.f()` calls `f`. On an optional, `.value()` still reads the value. The example `command` needs this for `Counter::value`.
- The example `command` gets `//@ modifies c` on `execute` and `undo` of the interface and of each class.

## Why

The examples `observer` and `command` change an object through its interface. After the call, the model knows only what the contract of the interface says about the new value. That is weaker than the real object, never stronger. The real object meets it, because its body proves its own contract, and the check shows that this contract gives the contract of the interface. A const function of the interface still reads the new value, so a caller can chain calls. Both examples also need a vector of `std::unique_ptr<B>`, slice six of 0165.

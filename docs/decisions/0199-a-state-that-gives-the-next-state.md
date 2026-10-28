# 0199: A state that gives the next state

Date: 2026-10-28. Status: decided. Builds on 0090, 0165, 0166, 0168, 0171 and 0172. Amends 0090 on the form of a pure body, and 0166 on the upcast. The example `state_object` gives each state a `const` virtual function `next()` that gives back a new state. Its context replaces the state that it owns with that one.

## Decision

A pure body can return early. Before its last `return`, it can hold `if (c) { return a; }`, and an `if` whose two branches each end in a `return`. The value of the body is `if c then a else b`, where `b` is the value of the rest of the body. Each branch is a pure body. A body that writes a local before a `return` keeps the rule of 0172.

A `const` virtual function of an interface can give back a `std::unique_ptr` of the interface. Its override gives back `std::make_unique<D>()` of a final class `D` over the interface, decision 0168. Dafny checks each override against the contract of the interface, decision 0165. The upcast of a class says that a call through the interface gives the value of the override, decision 0166. It says nothing of a function whose result holds the interface. That value holds the upcast, so the fact would define the upcast by itself, and Dafny cannot show that the definition ends. A call of such a function through the interface keeps the contract of the interface.

In a member function that writes its object, `f = e` writes a `std::unique_ptr` field `f` of the object. Here `e` is a call that gives a new `std::unique_ptr` of the type of `f`. The object that `f` owned before dies. It has no destructor of the model, as 0179 says for `= default`.

These keep the sentence of today:

- an early return in a body that writes a local or calls a function that is no pure function,
- `f = e` where `e` is no call, as `std::move(x)`,
- `f = e` of a field of a parameter.

## Why

The state pattern keeps the table of transitions in the states. Each state answers an event with the next state. Its `next()` is a few branches, each with one `return`. The context only knows the interface, so it proves the next state from the contract of the interface alone. The model already has the interface, the upcast and a `std::unique_ptr` field of an interface.

## What changes

The core reads a pure body with an early return. The shell leaves out of the upcast each function whose result holds the interface. The plugin writes `f = e` of a `std::unique_ptr` field from a call. Three fixtures follow the form of 0178. The example `state_object` proves.

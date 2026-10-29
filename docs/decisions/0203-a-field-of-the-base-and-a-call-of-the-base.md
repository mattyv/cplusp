# 0203: A field of the base and a call of the base

Date: 2026-10-29. Status: decided. Amends 0201. The review of 0201 found two quiet passes and two gaps. The reviewer decided the fixes.

## Decision

- A field of the base `B` through the class `D` has no rule, in a write and in a read. This holds for each form: `x = e`, `P::x = e`, `x += e`, `d.P::x = e`, `p->x` through a pointer, and `o->x` through an optional or a `std::unique_ptr`. The sentence is `a field of the base B: the translator has no rule for it yet.`
- A call of a member function `f` of `B` in code is a call of `B::f` on the field `'B`, as 0201 says. The call keeps the contract of `B::f`, and Dafny checks its requires lines at the call.
- The member function that the model gives `D` for a contract is only for a `B::f` with no requires line. A contract that calls a `B::f` with a requires line through `D` gets the sentence of a function with no function in the model.
- Each sentence names `B` and `D` by the plain name of the class, with no namespace, no `const` and no `*`.
- The change of a `D` into a `B` for a reference parameter `B&` has the sentence of 0201: `a change of D into its base B, which has data: the translator has no rule for it yet.`

## Why

The plugin read the field of the base as the field of the class with the same name. So a false ensures line about a field could prove when `D` has a field with the name of a field of `B`. That is the worst kind of failure: the proof says yes, and C++ says no. The member function of `D` had no contract, so a call in code lost the promise of `B::f`. And a requires line of `B::f` broke the proof of each class over `B`.

## What changes

The plugin refuses each form of a field of the base. It writes a call of `B::f` in code on the field `'B`. It gives `D` no member function for a `B::f` with a requires line. It names the classes by their plain names. The ceiling: a contract cannot call a `B::f` with a requires line through `D`. The upgrade path is to copy the requires lines through `'B`. Three fixtures show the forms.

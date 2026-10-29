# 0209: A const virtual function that writes a parameter

Date: 2026-10-29. Status: decided. Amends 0166 and 0169. The example `visitor` has `virtual void accept(Visitor& v) const = 0;`. It gives no value and writes its reference parameter. The translator refuses it with `a pure virtual function that gives no value: the translator has no rule for it yet.`

## Decision

Take a `const` pure virtual function of an interface that gives no value. It is a method of the interface, as a function that is not `const` is, decision 0169. It has no function and no upcast line. It takes its object in and does not give it back. Its reference parameters stand on its modifies line, decision 0108, and it gives each back. Dafny takes its contract as given.

Its override is a member function of 0096 that does not write its object. `prove` checks the override against the virtual function on the contracts, as 0169 says, with the sentences of 0165.

## Why

A `const` function that gives no value has an effect only through its parameters. So it is no function of the model, and the rules of 0169 for a method fit it. The visitor pattern needs it: `accept` sends the shape to the visitor, and the visitor changes.

## What changes

The core reads such a function as a method with no new object. The plugin stops its refusal. Three fixtures follow the form of 0178.

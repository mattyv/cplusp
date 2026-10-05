# 0030: Const reaches through a handle, and a function-local static is refused

Date: 2026-10-05. Status: decided. Follows the design-pattern round of examples.

## Decision

A `unique_ptr` reached through a const reference, or an element of a const container of them, gives const access only. A non-const call through it is refused under the row `unique_ptr`, which becomes `restrict`. A function-local static variable is refused under the new row `static_local`. Two matcher holes close with it. A `static_cast` between class references or pointers is refused as written, inside a template too. A pointer as a template argument is a stored pointer under the row `raw_pointer`.

## Why

The pattern round wrote the command pattern with a const vector of owned commands and ran them. The gate passed it. C++ const does not reach through a pointer. Under decision 0029 a const reference is a value in, so a change behind it is invisible to the model. Const must reach through the handle, or the model is wrong. The Meyers singleton passed the gate too. Its state is a function-local static, which has no name a caller's contract can list. So nothing about a call that changes it can be proved. A static data member has a name, and that is the shape the subset takes. The CRTP downcast passed because the upstream check skips template instantiations. A vector of raw pointers passed because the pointer rows looked at members and locals only.

## What changes

Four rows, two new pairs and two new banned lines. The battery case `static_local` moves to the gate side with a fixed version on a static data member. 74 rules, 60 enforced by the gate.

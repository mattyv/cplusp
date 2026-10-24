# 0182: A reference to a local through a call

Date: 2026-10-24. Status: decided. Builds on 0033 and 0181. The review of 0181 found a quiet pass: `const Pair& bad() { Pair x{1, 2}; return id(x); }` gives "ok: proved", although the caller reads a dead object.

## Decision

The row `return_ref_to_local` also follows a `return` through a call. In a function that returns a reference, a pointer or a span, the gate finds what the returned value can reach. A call that returns a reference, a pointer or a span can give back the object of the call. It can also give back any argument at a reference, pointer or span parameter. This includes a call into std, such as `std::max`. The rule holds for every `return`, with a call or without one. A range-for variable by reference reaches its range. A structured binding by copy is a local. If the value reaches a local of the function, a capture of a lambda or a parameter by value, the row refuses the `return`. These die when the function returns.

A parameter by reference, a static local and `this` live after the function returns, so a `return` that reaches only them stays allowed. Two examples are `return *this;` in a builder and `return items_.back();` in a member function. A pointer or a span parameter is a handle, and the object it points to lives too. A pointer or a span local is no handle. It reaches what it views. Two examples are `return *p;` and `return s[0];`. A global that escapes stays with the row `aliasing`, decision 0033. A temporary in the `return` stays with the translator, decision 0181.

ponytail: two ceilings. The gate reads every argument at a reference parameter as a value that the call can give back. This is so also when the callee gives back only its object. An iterator by value has no roots, decision 0033, so `*std::max_element(v.begin(), v.end())` of a local `v` passes the gate. The translator refuses that `return`, because the iterator is a temporary. The upgrades are to read the returns of a callee that the file defines, and to give an iterator the roots of its range.

## Why

The compiler warns when the `return` names the local, or reaches it through a container or a handle of std. It does not look into a function of the file, so a call between the local and the `return` hides the local. The model reads a return by reference as a return by value, so the prover cannot see the dead object. The gate is the place for this rule, because it sees the whole function and every call in it.

## What changes

The plugin adds the check `cplusp-return-local`. It follows the roots of a `return` as the check of a global that escapes does, decision 0033. The row `return_ref_to_local` lists it next to `clang-diagnostic-return-stack-address`. The sample pair of the row gets fourteen banned lines and eight allowed functions. A test with a team policy that loosens `array_span` and `raw_pointer` shows that a view local does not hide a local. The core needs no change.

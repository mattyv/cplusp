# 0096: A member function that writes its object takes it in and gives it back

Date: 2026-10-09. Status: decided. Step 5 of 0089.

## Decision

- A member function that is not `const` takes its object in and gives it back, as a value, decision 0029. Its method has the parameter `this` and the result `this'`, and also `result` when it gives a value. The body starts with `this' := this` and reads and writes `this'`.
- In its body, `f = e` writes a field `f` of a scalar type or an optional type. `f op= e` for `+`, `-`, `*`, `/` and `%` is `f = f op e`, with the conversions that C++ makes. The same holds for a local of a scalar type.
- In its contract, a bare field name in a requires line reads the object before the call. In an ensures line, a bare field name reads the object after the call, and `old(f)` reads it before the call. A pure member function in an ensures line, such as `valid()`, reads the object after the call.
- A call `o.f(a)` of such a function in code writes `o` back, so `o` must be a local. A call on a parameter, on a field or on an element has no rule yet. As a statement, `o.f(a);` is `o := f(o, a)`. As the start value of a local, `T x = o.f(a);` sets both `x` and `o`.
- A member function that is not `const` and that writes no field is still such a function. A function that returns a reference, such as `*this`, has no rule yet. Neither has a write to a field of a sequence type.
- The result type `void` is in the subset for such a function and for a free function. A `void` function has no `result`.

## Why

The examples change their objects through setters, such as `void assign(int32_t v) { n_ = v; }` and `void bump() { n_ += 1; }`. A function that writes its object is a function from the old value to the new one, so the value model of 0029 still holds. I checked the model by hand in Dafny. It has a counter, a setter that also gives a value, and a caller that calls it twice on a local.

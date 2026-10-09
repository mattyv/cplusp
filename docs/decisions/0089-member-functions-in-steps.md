# 0089: Member functions, in steps

Date: 2026-10-09. Status: decided. The sixth slice. Amends 0073 on what a struct may hold.

## Decision

- The sweep of the examples after the fifth slice found 161 refusals of a member function, more than all other refusals together. Member functions come in these steps, each proved before the next:
  1. A `const` member function of a struct. Its object is a parameter `this` by value, decision 0029. In code, a field of the object reads as a field of `this`. In a contract of the function, a name that is no parameter and is a field of the struct is that field of `this`. A call `o.f(a)` in code is a call of `f` with `o` as its first argument, and it stands alone, decision 0058.
  2. Private and protected fields. Access is a rule of the compiler and of the gate, and the model of a value does not change with it.
  3. A `const` member function whose body is one `return` of an expression with no call is also a Dafny `function`. A contract can call it, as in `valid()` or `o.valid()`.
  4. A constructor whose member init list gives each field a value is a value of the datatype, and its contract states facts about that value.
  5. A member function that is not `const` takes its object in and gives it back, as a value. `old(f)` in a contract reads a field before the call.
  6. `?:` in code and in contracts, and `operator()` as a member function.
- Steps 1 and 2 come first. A virtual function, a static member function, a function with a ref-qualifier, and a member template still have no rule.
- The Dafny name of a member function holds the name of its struct and a `'`, such as `c_Builder'valid`. C++ cannot write `'`, so no name of the author can clash with it.

## Why

A `const` member function reads its object and writes nothing, so it is a function of a value with one more parameter. The value model of 0029 holds, and the proofs of the fifth slice carry over.

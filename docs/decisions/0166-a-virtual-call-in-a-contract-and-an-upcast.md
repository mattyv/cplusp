# 0166: A virtual call in a contract, and an upcast at a call argument. Slice two of 0165

Date: 2026-10-20. Status: decided. Amends 0089, 0090, 0094 and 0165. This is slice two of 0165.

## Decision

- Each pure virtual function `f` of an interface `B` is also a function of the model, `c_B'f'`. It has the contract of `B::f` and no body, and Dafny takes it as given. The method of `B::f` also says `result == c_B'f'(this, ps)`. So two calls on one object with the same arguments give the same value.
- A contract of a virtual function of `B` can call a virtual function `g` of `B` on its object, such as `valid()`. The function `g` must come before `f` in `B`. Otherwise the translator refuses the contract line of `B::f` that reads `g`. The sentence is `the contract of B::f reads B::g, which comes later in B.`, then `Declare B::g first.` When `g` is `f`, the sentence is `the contract of B::f reads B::f itself.`, then `The translator has no rule for it yet.`
- A contract of a function with a parameter `const B& s` can call `s.f(a)`. That is the function `c_B'f'`. Dafny checks the requires lines of `B::f` at each such call, decision 0095.
- A call argument of a final class `D` to a parameter `const B&` is the upcast `f_D'B` of 0165. The model prints the upcast of each pair that has a check. It has one ensures line for each virtual function of `B`, in the order of `B`. The line is `ensures forall ps :: R_B@D && R_D ==> c_B'f'(f_D'B(this), ps) == c_D'f'(this, ps)`. A class that has no check has no upcast in the model. A call that needs one stops Dafny with `Dafny says: unresolved identifier: f_D'B.` The refusal of the class names the cause. A refusal of the call in the core is the upgrade path.
- `this->x` in a contract reads `x`, as decision 0089 reads a bare field name, and `this->f(a)` calls `f(a)`.
- A pure virtual function that gives no value has no rule yet. The translator refuses it at its line with `a pure virtual function that gives no value: the translator has no rule for it yet.`
- A constructor of a final class over an interface follows decision 0094. A local `const D d;` of a class with no field and no constructor has the value `S_D()`.
- The Axiom line of 0165 names a C++ class, never a name of the model. Two interfaces of one name show their full C++ names.

## Why

The example `strategy` passes a strategy to a function that reads only the contract of the interface. Its contract calls `s.valid()` and `s.apply(x)`, and it calls the function with two classes of strategy. Each piece above is one part of that path. The order rule keeps the functions of the model free of cycles. It also lets Dafny read each ensures line of an upcast with the lines above it. A hand model of `strategy` in this shape proves, except for one check. Dafny cannot prove `0 <= x * k` from `0 <= x` and `0 <= k`. So the check of `Scaled::apply` fails with the sentence of 0165. A later decision can help Dafny with a product.

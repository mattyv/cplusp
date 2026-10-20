# 0165: Virtual functions through an interface, in six slices. Slice one: an interface, a final class over it, and the check of each override

Date: 2026-10-20. Status: decided. Amends 0073 and 0089. The user asked the reviewer to choose the next direction, and accepted its plan on 2026-10-20.

## The plan

13 examples stop at a virtual function. The model has one shape for all of them, and the slices add it in this order.

1. An interface, a final class over it, a `const` virtual function, a call through `const B&`, and the check of each override. This decision makes slice one.
2. A virtual call in a contract, such as `s.valid()`, and an upcast at a call argument. Also `this->f` in a contract.
3. A virtual function that is not `const`.
4. `std::unique_ptr<B>`, `std::make_unique<D>`, and `p->f()`.
5. A field of type `std::unique_ptr<B>`.
6. A vector of `std::unique_ptr<B>`.

### The model

An interface `B` is a type of the model with no value that the model can see, `type S_B`. The shell gives every class the prefix `S_`, so the companion file cannot declare the name, decision 0083. The interface is in the table of structs for its member table. The core gives it no fields, and the shell prints `type S_B` for it and no datatype. Each pure virtual function `f` of `B` is a function of the model with the contract of `B::f` and no body. Dafny takes that contract as given. A call through `const B&` reads that function.

A final class `D` over `B` is a struct of 0073. For each pair of `D` and `B`, the model has an upcast `f_D'B` from a value of `D` to a value of `B`. For each virtual function `f` of `B`, the upcast has the line `ensures forall ps :: R_B@D && R_D ==> c_B'f'(f_D'B(this), ps) == c_D'f'(this, ps)`, with no `forall` when `f` has no parameter. Dafny takes this as given too. Both guards are necessary. Dafny checks that each call in the line meets its requires lines, and the lemma, not the upcast, shows that R_B gives R_D.

The model holds an upcast only with the check of each override of `D`. The check is a lemma for each virtual function of `B`. It reads the contract of `B::f` on the override. The parameters of the override take the place of those of `B::f`. The lemma is `requires R_B@D ensures R_D ensures var result := c_D'f'(this, ps); E_B@D`, with an empty body. Dafny reads the first ensures line when it checks that the call in the second meets R_D, so each half fails on its own line. Dafny proves two things from the body of the override. First, the requires lines of the override follow from the requires lines of `B::f`. Second, the override meets the ensures lines of `B::f`. Without these lemmas, the two things that Dafny takes as given can prove `false`. The review showed this.

`prove` prints one line for each interface in the model, before its verdict:

```
Axiom: model: B: a call through B runs an override that keeps the contract of B, C++23 [class.virtual]. Each override of B in this file is checked against that contract.
```

### Conditions

- A class over an interface must be `final`. Otherwise a `const D&` can name an object of a class derived from `D`, whose override differs. The gate passes such a class, so the translator refuses it.
- An override of another translation unit gets its check when `prove` runs on that unit. A call through `B` with no override in view rests on the contract of `B`, as a call of a trusted function does. Such a file proves on the contract of `B` alone, and the Axiom line is the only trace.
- The gate bans a downcast, a slice and a virtual call during construction. When constructor bodies come, the translator keeps refusing a virtual call in them.
- A Dafny `trait` can do the same check with the flags `--type-system-refresh --general-traits=datatype`. Dafny calls these traits experimental, and the review found two gaps in what the prover can see through them. They are the upgrade path when they are no longer experimental.

## Decision for slice one

- An interface is a class with no field and no base, whose members are pure virtual `const` functions and a destructor `= default`. A defaulted virtual destructor is nothing in the model.
- A class with a base that is no interface has no rule yet, as before: the translator refuses its member functions by their kind.
- A contract of a virtual function of an interface reads its parameters and `result`. A call of another member in it comes in slice two.
- The translator refuses a class over an interface that is not final, at its line. The sentence is `D derives from an interface and is not final. Mark it final.` For each class with a base, the shell gives the core three things. They are its key, the keys of its interface bases, and whether it is final. The core makes the refusal.
- A final class whose bases are interfaces is a struct of 0073. Each override is a member function of 0090, and it must have a function in the model, so its body is pure.
- The core finds the virtual functions of `B` among the functions whose first parameter is `this` of `B`. Each must be in the member table of `B`. A name that two of them share is not in it. So the translator refuses each class over the interface, at the line of the interface. The sentence is `B has two virtual functions of one name. The translator has no rule for it yet.`
- For each virtual function of each base, the class has exactly one override, with the same parameters and result. Otherwise the translator refuses the class with `D has no override of B::f.` The translator refuses an override that has no function in the model with `the override of B::f in D has no function in the model, so the translator cannot check it.`
- A failed check is a failed proof with its own sentence. The requires half gives `the override may require more than B::f.` The ensures half gives `the override may not keep the promise of B::f.` Each shows the contract line of `B::f`. A requires line of an override that reads a field can never pass the check. An override is callable in every state of its object.
- A parameter `const B& s` reads `s.f(a)` as a call of `B::f`. A local, a result, a field or a pointer of an interface type has no rule.
- A call `s.B::f()` with the name of the class runs no override, so it has no rule yet. A body of a pure virtual function has no rule yet either. It runs only through such a call, and nothing checks it against the contract of `B::f`.
- Slice one prints no upcast and no function of `B::f`, because no code changes a `D` into a `B` yet. The method of `B::f` has its contract and no body, as a trusted function has, decision 0102. Slice two prints the upcast with the first call that changes a `D` into a `B`.

## Why

The reviewer tested two models in Dafny and chose this one. It needs no experimental flag, it is the shape of the hand models of the examples, and the trust is one line for each interface. The lemma is the check of Liskov. An override may promise more than the base, and it may require less. The `final` rule closes the one gap that the gate leaves open.

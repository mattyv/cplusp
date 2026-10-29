# 0201: A base class with data

Date: 2026-10-29. Status: decided. Builds on 0073, 0090, 0094, 0165 and 0166. Amends 0165 on a class with a base that is no interface. The example `multiple_inheritance` has a class `Crate` over a base `Item` with a field and over two interfaces.

## Decision

A class `D` can have one base class `B` with data, next to its interfaces. `B` must be a public base that is not virtual. `B` must be a plain struct of 0073 with no base and no virtual function. `D` must be final when it has an interface, as 0165 says.

The model gives `D` one more field, before its own fields. The field holds the value of `B`. Its name is `'B`, so no C++ field can have the same name. The constructor of `D` starts the field with `B(args)` of its init list. `B(args)` is a call of the constructor of `B`, decision 0094.

A call of a `const` member function `f` of `B` on an object of `D` is a call of `B::f` on the field `'B`. For each such function, the model gives `D` a member function `f` with the parameters of `B::f`. Its body is `return 'B.f(args);`. So `d.f()` and `this->f()` read in a contract as any other member function, decision 0090. `D` gets no such function when it declares its own `f`, because C++ hides `B::f` then.

The rest has no rule yet. The translator refuses each of these at its line:

- A call through `D` of a member function of `B` that is not `const`. The sentence is `a call of a member function of the base B that is not const: the translator has no rule for it yet.`
- A change of a `D` into a `B`, such as an argument for `const B&`. The sentence is `a change of D into its base B, which has data: the translator has no rule for it yet.`
- A read of a field of `B` through `D`. The sentence is `a field of the base B: the translator has no rule for it yet.`

## Why

A base with data is the common form of reuse in C++. The value of `D` holds the value of `B`, so a field is the true model. The hand model of the example has the same shape. C++ finds `d.f()` among the members of `B`. A member function of `D` for it does the same, so the contract language needs no new form.

The member function that the model gives `D` is new trust in the plugin. It is the plugin that reads the change into the base that clang makes for `d.f()`. The sample pairs and the fixtures are its evidence.

## What changes

The plugin gives `D` the field `'B`, the start of the field from the init list, and a member function for each `const` member function of `B`. It writes a call of `B::f` on `D` as a call of the member function of `D`. It writes the three refusals. The list of interfaces that the shell gives the core leaves out `B`. The core needs no change. The example `multiple_inheritance` marks `Crate` final. Three fixtures follow the form of 0178.

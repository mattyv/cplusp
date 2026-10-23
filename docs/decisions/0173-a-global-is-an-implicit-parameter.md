# 0173: A global that a function lists is an implicit parameter of the function

Date: 2026-10-23. Status: decided. Builds on 0011, 0035, 0102, 0108 and 0111. The user asked to make every example prove, and the reviewer ordered the work. This is step one of that plan, for free functions. Decision 0174 does static member functions.

## Decision

A global or a static data member that a function lists on its `modifies` line is a reference parameter of the function, decision 0108. The method takes it in as `v_total` and gives it back as `v_total'`. A global on the `reads` line only is a parameter by value. A function that lists no global gets no parameter. The listed globals come after the written parameters, in the order of their definitions in the file. A static data member has its qualified name as one word: `Tally::count_` is `v_Tally'count_`.

The contract rules are those of a reference parameter. `total` in a requires line is the value before. `total` in an ensures line is the value after. `old(total)` is the value before.

A call gives the callee each global it lists. The argument is the parameter of the caller with that name. A write-back of a global goes to the reference parameter of the caller, as a write-back to a local does, decision 0108.

A reads line names a global, as a modifies line does. A reads line of any other form has no rule.

The translator refuses five forms. Each has its sentence.

- A function with no `reads` and no `modifies` line names a global. The sentence is the one for an unresolved name.
- A function with a `reads` line calls a function that lists the same global on its `modifies` line. The sentence is "f changes X. The caller lists X on its reads line only."
- A global that the function lists has the name of a parameter or a local of the function. A global that the function does not list can share its name with a parameter or a local. Then the name means the parameter or the local, as in C++. The sentence is "X names a global and a parameter or a local."
- A member function lists a global on a `reads` or a `modifies` line. The sentence is "a member function that lists a global: the translator has no rule for it yet."
- A global has a type that no struct field can have. The sentence is "a global of this type: the translator has no rule for it yet."

## Why

Decision 0011 lists globals in contracts. Decision 0035 checks the lines at the gate. The prover had no model, so no function that touched a global proved. A reference parameter is a model the core already has and proves. The frame comes with it: a function can change only the globals it takes as reference parameters. A body that writes an unlisted global names no parameter and no local, so the translator refuses the name. The gate refuses two names for one object, a global and a reference argument that reaches it, under the row `aliasing`. The sentence for a reads line that meets a modifies line names the fault. The sentence of 0108 for a write-back would name the mechanism.

## What changes

The core gains one pass before `translate_unit`. The pass adds the listed globals to the parameters of each function. It types each global name in the body by them. It gives each call the globals of its callee. It consumes the reads lines. The shell runs the pass. The plugin gives each global and each static data member with its type and line. Three fixtures: `model-state.cpp` proves, `model-state-wrong.cpp` fails at the named lines, `model-state-refuse.cpp` refuses with the sentences. The example `global_state` proves.

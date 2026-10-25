# 0189: A call of a plain member function

Date: 2026-10-25. Status: decided. Builds on 0089, 0090, 0095, 0166 and 0172. Amends 0172 on a pure body that calls a member function. The example `crtp` calls a member function of its field in a member function that only reads.

## Decision

A plain member function is a `const` member function whose body is one `return` of an expression with no call. It writes no reference parameter. Its function is in the model, as 0095 marks it, so its contract has a model too.

A call of a plain member function is its function in place, in each place of code. Its object can be the object of the caller, a field, a parameter or a local. So the call can stand on the right of `&&` or `||`, in a branch of `?:` and in a loop condition. A call of a `const` virtual function of an interface can do the same, decision 0172. Dafny checks the requires lines of the function at each call. The sentence is `a requires line of the callee may not hold.`, as for a method.

A body that calls only plain member functions, and no other function, can be a pure body of 0090. So a member function that calls one gets a function in the model, and a contract can call it. This replaces two rules of 0172. A call of a member function of its own class no longer makes the caller a method, when the callee is plain. A call of a pure member function of another struct now has a rule, when the callee is plain.

A call of any other member function keeps the rules of 0104 and 0172. This holds for a member function whose body holds a call, or has more than one statement. It also holds for one whose contract has no model. The order on the functions comes from the form: a plain member function calls no function, so no cycle of calls can form.

## Why

A class reads a class inside it through small accessors, as `step_.valid()` and `step_.apply(x)`. Each accessor is one expression. Its value depends only on its arguments. So the call can be the function of the model in any place, as the call of an interface is. A plain callee calls nothing, so the model of each function stays finite. That is the order that 0172 asked for.

## What changes

The core reads a call of a plain member function as its function, when the table marks the callee as pure. The plugin and the shell need no change. Three fixtures follow the form of 0178. The fixture of 0172 gives its own-class callee a call in its body, so it keeps its refusal. The example `crtp` gets an explicit instantiation for each instance, as 0188 says, and proves.

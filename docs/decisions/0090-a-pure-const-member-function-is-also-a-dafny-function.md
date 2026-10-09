# 0090: A pure const member function is also a Dafny function

Date: 2026-10-09. Status: decided. Step 3 of 0089.

## Decision

- A `const` member function is pure when its body is one `return` of an expression that holds no call. A pure member function is also a Dafny `function`, named as its method with one more `'`, such as `c_Counter'valid'`. Its parameters are those of the method. Its requires lines are the requires lines of the method. Its body is the expression of the `return`.
- The method of a pure member function gains the line `ensures result == F(this, ...)`, with F its function. So a caller that calls the method in code knows the value of the function.
- A contract can call a pure member function. Inside a contract of a member function of the same struct, `f(a)` passes `this`. Anywhere, `o.f(a)` passes `o`, where `o` is a path of the struct. Dafny proves the requires lines of the function where the contract calls it.
- A member function that is not pure has no function, and a contract that calls it is refused.
- A pure body holds no call, so no function calls another, and none recurses.

## Why

The contracts of the examples call member functions such as `valid()`, and Dafny calls no method in a contract. The body of a pure member function is the expression that its contract would state. The model was checked by hand in Dafny with `valid` and `next` of a counter.

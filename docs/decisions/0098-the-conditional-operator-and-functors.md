# 0098: The conditional operator, and a struct with an operator()

Date: 2026-10-09. Status: decided. Step 6 of 0089.

## Decision

- `c ? a : b` is in the subset in code and in contracts. Its Dafny form is `if c then a else b`. Dafny checks each branch only where its condition holds, as C++ evaluates only one branch. A branch holds no call, as any other expression of code, decision 0058.
- In a contract, `?:` binds more loosely than `||` and more tightly than `==>`, as in C++. The middle part reaches to its `:`. The last part is a conditional again, so `a ? b : c ? d : e` is `a ? b : (c ? d : e)`.
- `operator()` of a struct is a member function, with the rules of 0089 to 0096. A call `f(x)` in code, where `f` is an object of the struct, is a call of that member function with `f` as its first argument.
- In a contract, `f(x)` where `f` is a parameter or a field of the object, of a struct type, calls the function of its `operator()`. That `operator()` must be pure, decision 0090. If not, the line is refused with `NotPure`, decision 0095.
- The Dafny name of `operator()` of the struct `S` is `c_S'call`. A C++ name cannot hold `'`, so no name of the author can clash with it, decision 0089.
- A template that takes a functor type still has no rule. Each type that it is used with would need its own model.

## Why

The examples choose between two values with `?:` in code and in contracts, as in `x < limit ? x : limit`. The example `callbacks` passes a functor, a struct with a `const` `operator()` that has its own contract, so that each call is a direct call.

## What changes

The core gains the conditional in code, in contracts and in the parser, with the tokens `?` and `:`. It reads a call of a parameter or a field of a struct type in a contract as a call of `operator()`. The core names `operator()` by a fixed id that the shell gives to the text `operator()`. The plugin writes `?:` and the calls of `operator()`. The shell cuts `?` and `:`, and prints the conditional and the name `call`.

# 0179: A move of a struct

Date: 2026-10-24. Status: decided. Builds on 0094, 0108, 0171 and 0178. The example `raii_handle` moves a handle into a function and into a local.

## Decision

A parameter `T&&` of a struct `T` is a reference parameter, as `T&` is, decision 0108. A function that writes it lists it on the `modifies` line. A `T&&` parameter of any other type has no rule.

`std::move(x)` of a struct, as the argument of a `T&&` parameter, passes `x` by reference. The callee writes `x` back. `T y = std::move(x);` calls the move constructor of `T` with `x` by reference. After the call, `x` has the value that the move constructor gave it. `x` still dies at the end of its block, decision 0178.

A constructor can have a body. The init list runs first. Then the body runs. The body can hold the statements of a free function. They use the parameters of the constructor and the globals on its `modifies` line. It cannot read or write a field of the new object, and it cannot use `this`. The translator first computes each value of the init list into a fresh local, in the order of the fields. Then it runs the body and builds the result from the fresh locals. The `return` that builds the result has the line of the constructor. So a body that writes a parameter cannot change a value that the init list read. A constructor with an empty body keeps the form of 0094.

A move constructor `T(T&& other)` is such a constructor. It lists `other` on its `modifies` line, as each reference parameter does, decision 0108. Its init list reads `other`, and its body writes `other`.

A move constructor needs a destructor in its struct. A destructor `= default` is no destructor of the model. Then the rules of 0178 keep each value of the struct in its block. So C++ calls the move constructor only at the start of a local. Without a destructor, C++ also calls the move constructor at `return x;`, for a parameter by value, for a field and in a vector. The model has no call there. A compiler can also skip the call at `return x;`, so the model cannot know if it runs.

`std::move(x)` of a struct in any other place keeps the refusal of 0171.

These forms have no rule:

- a field or `this` in the body of a constructor, at the line of the statement. The sentence is "a field in the body of a constructor: the translator has no rule for it yet."
- a `T&&` parameter of a type that is not a struct, at the line of the function.
- a move constructor in a struct with no destructor, at the line of the move constructor. The sentence is "a move constructor in a struct with no destructor: the translator has no rule for it yet."
- a copy or a move by a constructor that the model cannot call, at the line of the statement. An example is a constructor that the file only declares. The sentence is "a copy or a move by a constructor that the model cannot call: the translator has no rule for it yet."
- a `return` in the body of a constructor, at the line of the `return`. It keeps the sentence of a node with no rule.

## Why

A move-only handle gives its open state to a new owner and leaves the old one closed. The contract of the move constructor says so: `requires other.valid()`, `modifies other` and `ensures valid() && !other.valid()`. With `other` as a reference parameter, the value model already has the words for it. The destructor of the old handle then releases nothing, and the contract of the destructor says so with `old(valid())`.

C++ runs the init list before the body. A move constructor reads the source in its init list and clears the source in its body. The fresh locals keep the values of the init list, so the model sees the same order.

## What changes

The plugin writes a `T&&` parameter of a struct as a reference parameter that the function can write. It writes `std::move(x)` of a struct, as the argument of such a parameter, as `x`. It writes a constructor with a body as the fresh locals, the statements of the body, and a `return` of the struct. It refuses a move constructor in a struct with no destructor. It refuses a copy or a move by a constructor of the file that it cannot write as a call. The core needs no change. Each move constructor lists `other` on its `modifies` line, also in `raii_handle`. The example `raii_handle` lists `h` on the `modifies` line of `consume`, because the function writes it through the move. Three fixtures follow the form of 0178. The example `raii_handle` proves.

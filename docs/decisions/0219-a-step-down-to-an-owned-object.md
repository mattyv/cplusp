# 0219: A step down to an owned object

Date: 2026-10-29. Status: decided. Amends 0218 and 0173. With the check of 0218 as written, the core refused the example `decorator`. `Capped::valid` calls `inner_->valid()` through the interface `Component`, and `Capped::valid` is an override of `Component::valid`. So the call graph had a path back, but each lap of the recursion runs on a smaller object.

## Decision

- A call whose object is a `std::unique_ptr` field of `this`, as `inner_->valid()`, is a step down the tree of owned objects. A path of such steps only goes from an object to a part of it, so it ends.
- For such a call, only a path back to `g` with one or more other steps has no rule. For each other call through an interface, any path back has no rule, as 0218 says.
- The calls of a bare block and of the lambda of `std::sort` count as calls of the body. This holds for the call graph of 0218 and for the globals of 0173.

## Why

The objects that a file can make with `std::make_unique` and `std::move` form a tree. Each one owns its parts. The gate refuses a move of an object into its own field. In the model, each value is a finite tree too. So a recursion that only goes down the tree ends. A decorator, a chain of wrappers over one interface, is this case. A step that is not down can go to any object, so it keeps the rule of 0218. The calls of a block and of a sort lambda run in the body, so a check that leaves them out can miss a call.

## What changes

The core reads, for each call, whether its object is a field of `this`. It leaves out the overrides of such a call from the steps that can come back. A destructor still has an edge from each function, which is sound and can refuse more than it must. A later decision can narrow it.

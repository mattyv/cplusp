# Examples

One folder per row of the policy that verified code may use: every `allow`, `restrict` and `trusted_only` row. Each shows the C++ as the bot should write it under the row, and the Dafny the bot writes for it by hand, decision 0017. The battery under `divergence/` shows where a naive model goes wrong. This folder shows the right way, one row at a time.

Each folder has:

- `example.cpp`: C++ under the row, with its `//@` contract. It passes the gate.
- `example.dfy`: the Dafny model of it, under the rules in `skills/cplusp-dafny/SKILL.md`. It verifies.
- `trusted.cpp`: for a `trusted_only` row, and for a larger example that needs one, decision 0031. The trusted function that uses the construct, behind the contract `example.cpp` declares. The gate refuses it, under that row alone for a row's folder, which shows the construct is there. The prover never reads it. `example.cpp` holds the declaration with the contract and a verified caller. The declaration carries `CPLUSP_TRUSTED("reason")` from `include/cplusp.h`, the marker of docs/plan.md. The gate does not read the marker yet, so the body lives in its own file.

The test `every_row_the_bot_may_use_has_an_example` in `crates/divergence` runs the gate on every `example.cpp` and `trusted.cpp`, and Dafny on every `example.dfy`. A contract in an example is a real one: it says what the function promises, never only that it returns.

## How the Dafny follows the C++

- A free function is a method with the same contract.
- A member function's contract uses the implicit `this`, decision 0028. Members are in scope by name and are never listed in `modifies` or `reads`. A non-const method may change any member, a const method none. The class invariant is a const member function, `valid()`, and every public method says `requires valid()` and `ensures valid()`.
- The model has no heap, decision 0029. An object is a `datatype`. A const member function is a `function` over the value. A non-const member function is a method that takes the object in and gives it back, `c' := bump(c)`. `old(x)` in the C++ is the value on the way in, `x` the value on the way out. The invariant is a predicate over the value. A constructor is a method that returns the value. A destructor is a method called where the block ends.
- A class template or a function template has no model. Each type it is used at gets its own datatype and methods.
- A pointer or a `unique_ptr` is an `Option<T>` value. An interface is an opaque type with its contract as the only functions known about it. An implementation proves it meets that contract on its own type. The upcast is an axiom that says only `f(As(x)) == f_impl(x)`, and a lemma proves `f_impl` meets the interface contract. Without the lemma the two axioms can contradict.
- A trusted function is a `method {:axiom}` with its contract and no body.
- A global or a static is a field of one `State` value that every function that touches it takes in and gives back.
- A reference is a parameter only. Two non-const reference parameters of one type carry `requires &a != &b`. No `class`, `trait`, `modifies`, `reads`, `old` or `new` appears in a model, and the test `the_model_has_no_heap` keeps it so.
- A `double` is a real through `Double.dfy`, with one rounding per operation.

## Larger examples

The rows show one construct at a time. The larger examples combine several, the way a bot writes real code, and push the gate and the model where a single row does not. Each has the same files and the same test. The folders are named after what they build.

To ask "what about this pattern", add a folder with the C++ as you would write it and the Dafny for it. The test picks up every folder. When the gate refuses the C++, that is the answer, and it is either a finding about the gate or a limit to write down.

- `stack_template`: a class template at two types, with an invariant, members as state, and callers that prove from the contracts.
- `sorted_insert`: an insert into a sorted vector that keeps it sorted. A quantified contract, a loop invariant, `old()`.
- `state_machine`: an `enum class` of states and a transition table in a switch. The model is a datatype and a match.
- `parse_digits`: digits from a span into an `std::optional<int32_t>`, with a value function the contract names and an overflow bound.
- `dot_product`: two spans, a 64-bit accumulator, bounds that keep the sum in range, a spec function the contract names.
- `shape_area_sum`: an interface with a contract, two final classes, a vector of `unique_ptr` to them, and a sum that proves from the interface alone.

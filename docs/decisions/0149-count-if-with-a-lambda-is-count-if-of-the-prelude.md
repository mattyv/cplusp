# 0149: count_if with a lambda is CountIf of the prelude

Date: 2026-10-14. Status: decided. Amends 0064. The user chose this direction on 2026-10-13.

## Decision

- In code, `std::count_if(v.begin(), v.end(), f)` has a rule. `v` is a sequence parameter, decisions 0064 and 0145. `f` is a lambda written in the call. It has one parameter of the element type, by value or by `const&`. It captures by value only, and it has no init capture. Its body is one `return e;`, and `e` holds no call.
- The model is `CountIf(v, (x: T) => e)`, as an `int64`, since `count_if` gives a `std::ptrdiff_t`. The lambda reads the parameter and each capture by its name. A capture by value copies the variable when the call starts. The gate refuses a change of the variable in the same expression. So the name holds that value.
- The prelude defines `CountIf`. It counts the elements for which the test holds, and it ensures that the count is at most the length. Dafny proves it, so it adds no axiom. The plan lists it as part of the trusted model of `std::count_if`.
- A contract names a predicate or function of the companion file that counts, such as `Count(v, k)`. The companion defines it with `CountIf` and a lambda that says the same test. Dafny matches the two lambdas when they say the same test. When they do not, the proof fails, and the author can write a lemma.
- A companion file cannot declare the name `CountIf`, decision 0083.
- These still have no rule: any other algorithm, and a range other than `v.begin(), v.end()`. Also a function or a functor in place of the lambda, an init capture, and a body of more than one statement.

## Why

The examples `lambdas` and `algorithms` count with `std::count_if` and a lambda. The plan allows a lambda passed straight to an algorithm on a short trusted list, and the gate already holds the limits on captures. A test model with this shape proved three runs in three. It matched `x > k` in the code with `x as int > k` in the companion, and it refused `x >= k`.

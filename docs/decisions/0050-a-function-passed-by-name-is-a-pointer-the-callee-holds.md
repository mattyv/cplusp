# 0050: A function passed by name is a pointer that the callee holds

Date: 2026-10-07. Status: decided. Amends 0049, whose first paragraph names a call that only constants reach.

## Decision

A function passed by name to a call becomes a pointer that the callee holds. The callee stores it or takes it by reference, and it calls through that place. The gate does not follow the pointer into code that the file does not write. So a call such as `std::sort(b, e, less_than)` is a finding of `function_pointers` at the call, also when only a constant reaches the place. A lambda passed straight to the std call is the way. The row `lambdas` allows it, and the compiler makes a direct call to it.

## Why

The review of the 0049 green step found that `std::sort(b, e, less_than)` with a verified `less_than` became a finding. By 0049's first paragraph the call has a name, because only the constant reaches it. To pass it, the gate would follow each pointer argument into each library function and back to its caller. That is the list of excuses that 0049 dropped, and three reviews found holes in it. The row already says to use direct calls or a template parameter. A lambda is a template parameter, and the prover needs no contract on a target that it can see.

## What changes

Nothing in the gate. The sample pair of `function_pointers` pins both ways: the name is refused, and the lambda is allowed. The marks of 3fcfed4 in the pairs of `global_state` and `concurrency` stand.

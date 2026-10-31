# 0223: A trusted body can call each function

Date: 2026-10-31. Status: decided. Amends 0102, 0218 and 0222. The review of 0222 found a recursion that never ends and that proved. A trusted function `spawn` made a local `Guard`, and the destructor of `Guard` called back through the interface `Log` into the function that called `spawn`. The plugin writes no body for a trusted function, decision 0102. So in the call graph of 0218, a trusted function called nothing and ended no life, decision 0222.

## Decision

In the call graph of 0218, a trusted function has an edge to each function of the file. So a call through an interface in a function that a path through a trusted function reaches has no rule, as 0218 says.

The contract of a trusted function is a promise that the function returns and then holds its ensures lines. A trusted function that does not return breaks that promise, as a false ensures line does.

## Why

The core cannot read a trusted body, so it cannot know which functions the body calls or which lives it ends. An edge to each function is true for each body. It is also the rule that each function had for the destructors before 0222. A recursion that goes only through trusted bodies has no call in the model that the check can refuse. The `Trusted:` line names each such function, and the person who marks it takes on its promise. The plugin could write the calls of a trusted body for the graph only. That is the upgrade path if this rule refuses too much.

## What changes

The core gives each trusted function an edge to each function of the file. Three fixtures hold the cases. The destructor of a local in a trusted function comes back. A trusted helper that calls through the interface comes back. A call result that a by-value parameter ends comes back, which pins one more rule of 0222.

# 0176: A free function with one return has a function twin that a contract can call

Date: 2026-10-24. Status: decided. Builds on 0090, 0104, 0172 and 0174. The example `bit_flags` calls `has(flags, flag)` in its contracts.

## Decision

A free function gets a function twin when its body is one `return` with no call. It must have no reference parameter and no global on a `modifies` line. That is the rule of a const member, decision 0090, and of a static member function, decision 0174. The twin has the name of the method with a prime, `c_has'`. The method gets the line `ensures result == c_has'(params)`.

A contract can call the twin by the name of the function, `has(result, flag)`. The call converts the arguments to the types of the parameters. The globals of the function come after them, as for a static, decision 0174. The translator refuses a contract that calls a free function with no twin.

The sentence for a member, a static or a free function with no twin is now one. It is "f is no pure function. A contract calls a function with one return and no write."

A call of such a function in code stays under decision 0104. It stands alone, in the start value of a local or in a `return`. In the middle of an expression it is a call out of place. The example `bit_flags` holds the two calls of `has` in two locals for that reason.

The translator refuses a name that is a function of the file and also a function of the companion file, at the contract line. The sentence is "f is a function of the file and of the companion file. Rename one."

## Why

An operator is a pure function, and the prover calls it as one, says the example `operator_overloading`. The example `bit_flags` does so with `has`. Decision 0090 gave a twin to a const member only, because a free function had no table to be found in. Decision 0174 made that table for statics. A free function is a static with no class. A call in a contract is the only way to give the test of one flag a name. A body with a call stays out. So a recursive function keeps its method and its `decreases` line. A call in the middle of an expression stays out too. The rule of decision 0172 lifts it for a const virtual function, whose function has no body, so no function can reach itself through it. A twin has a body, and a function that reaches itself through its own twin would need a proof of its own. No example needs it yet.

## What changes

The shell lists the free functions with a contract and no object in the table of structs, under one entry for the file. The entry has a key that no C++ name can spell, no field and no line of its own. The shell prints no datatype for it. The core marks such a function pure under the rule of decision 0090, with no call in the body. It finds the function by name, as it finds a static. The plugin changes nothing. One core test said that a free function never has a twin. Now it says that the function has one when the file lists it, and none when the table is empty. Six cli lines said "is no pure member function of its struct". Now they say the one sentence. Four fixtures: `model-free-twin.cpp` proves, `model-free-twin-wrong.cpp` fails at the named lines, `model-free-twin-refuse.cpp` refuses with the one sentence, and `model-free-twin-clash.cpp` with its companion file refuses the clash. The example `bit_flags` proves. Its comment on the model says the bit functions of the prelude, not `bv32`. Its last function holds the two calls of `has` in two locals.

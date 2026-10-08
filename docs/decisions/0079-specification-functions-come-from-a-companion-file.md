# 0079: Specification functions come from a companion Dafny file

Date: 2026-10-08. Status: decided. Closes the question that 0072 left open.

## Decision

- A contract can call a specification function, such as `Wellformed(n)` or `Height(n) <= 1000`. C++ has no place to define one. So the author writes each one in Dafny, in a companion file next to the C++ file. For `find.cpp` the file is `find.spec.dfy`.
- The companion file holds only `function` and `predicate` declarations, and comments. Each declaration has a body. The shell refuses the file when it holds any other word at the start of a declaration. It also refuses the file when it holds an attribute `{:`, `assume`, `expect`, `include`, `import`, `method` or `lemma`. A function with a body is a definition, and Dafny checks that it ends. So the file can add no axiom.
- A function with no body is an axiom. `prove` runs Dafny with `--allow-warnings`, because a bare method of 0058 has no body either. With that option, Dafny proves from a function with no body. Dafny reports each declaration with no body as a warning. So `prove` refuses a run with such a warning on a line of the companion file. The scan and the warning check each other.
- The file uses the Dafny names of the model: `S_Node`, `f_children`, `Vec`, `Option` and the integer newtypes. A parameter that is an integer in C++ is an `int` in the function, because a contract reads each integer as an exact integer, decision 0060.
- In a contract, a call `F(e1, e2)` names a function of the companion file. Each argument is an expression of the contract. The translator refuses a call to a name that the file does not declare.
- `cplusp prove` and `cplusp model` read the companion file when it exists, and put its text after the prelude.

## Why

`radix_find` states its result with `Stored`, `Wellformed` and `Height`, which are recursive definitions over the tree. A contract in C++ syntax cannot define them. A companion file keeps them in the language that checks them. The list of allowed words is short, so a review of the file is a review of definitions only.

## What stays trusted

The check of the file is a scan of its words in the shell. It is a trusted edge until the lexer moves into the core, decision 0077. The meaning of each function is the author's claim about what the code should do, as each contract line is.

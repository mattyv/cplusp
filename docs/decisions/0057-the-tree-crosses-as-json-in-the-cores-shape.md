# 0057: The tree crosses as JSON in the core's shape, and the first slice is small

Date: 2026-10-08. Status: decided. Amends 0056 on the format of the tree and on the first slice.

## Decision

- No external translator. Nothing that is kept up turns C++ into Dafny. Each tool that reads C++ gives its own target, such as Boogie, Rocq, constraint clauses or bounded checks. Each loses the source names, the `//@` lines and the value model of 0029. Each would also be a large edge that nothing proves.
- The clang-tidy plugin writes the tree. It holds the parsed tree, the calls that the compiler resolved and the lowered form of 0037. So it is the one reader of the source. Clang's own JSON dump stays out, because it would be a second reader, and its fields change between releases.
- The tree crosses as JSON in the shape of the core's types. Each object is one function, with names and kinds as numbers and the table of their text beside them. The shell reads it with `serde_json`, the one new dependency. The plugin keeps each implicit node, such as an implicit cast, and gives each call the callee that the compiler resolved. So the core refuses what it does not know, and the proof that no unknown node is skipped covers it.
- The shell cuts each `//@` line into tokens. The core parses the tokens, and the proof says that the parser ends and reads every token or refuses the line.
- The first slice is `clamp` from `examples/saturating_add`: comparisons, `&&`, `==>`, `if` and `return`. The slice grows through locals and casts, calls, structs, `std::vector`, `std::span`, loops and recursion. `radix_find` comes after that.

## Why

A review of the candidates found SMACK, cpp2v, ESBMC, CBMC, Frama-C and SeaHorn. None gives Dafny, and none would leave more of the work proved than the core does. A contract in the subset is arithmetic on exact integers, so a contract line needs a real parser, not a copy. That parser is part of the core. `radix_find` needs loops, the invariants of loops and hints for the prover, and the contract language has none of these yet.

## What changes

The core gains the translator and the contract parser, with their proofs. The plugin gains a dump of each function as JSON, and the shell gains a command that prints the Dafny model of a file. `serde_yaml`, which the shell uses for the fixes of clang-tidy, is archived. Its replacement is a later change.

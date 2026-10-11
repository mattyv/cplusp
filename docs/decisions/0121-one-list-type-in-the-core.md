# 0121: One list type in the core

Date: 2026-10-11. Status: decided.

## Decision

The core has one generic list type, `List<T>`, in place of a list type for each kind of item. A list of names and types, a list of statements and the other lists of the model are each a `List` of their item. A list of pairs `(key, value)` gets one function that finds the value of a key. A key is in the list when that value is `Some`. A list of keys gets one function that tells whether a key is in it. Each function has a spec and a proof, as before. The rules that read a list use these functions, and not a walk of their own.

The core does this in steps. Each step keeps every test, every proof and the output of the gate and of `prove` the same. A step changes no rule.

- Step 1: the list type, the functions for a list of pairs, and the lists of names and of parameters.
- Step 2: the lists of functions, of structs, of members, of contract lines and of arguments.
- Step 3: the lists of the Dafny model. The cases of a `switch` become a list of blocks, so a rule that reads statements also reads cases.

## Why

The core has 18 list types. Each has its own functions to find, to test and to add an item, and two pairs of them are copies of each other. The user asked for a smaller core with no weaker proof. A spike showed that Verus proves a generic list, and a tree of statements through it, with the same proofs as before. The spike saves about 700 to 800 of 6,700 lines. The two copies of each rule stay. Verus proves the rule that runs against the rule that the proofs read, and no other form keeps that proof.

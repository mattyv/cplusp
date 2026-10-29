# 0206: A variant that can lose its value

Date: 2026-10-29. Status: decided. Amends 0202. The review of 0202 found a quiet pass and three gaps. The reviewer decided the fixes.

## Decision

- Each alternative of a variant must be trivially copyable and at most 256 bytes. Any other variant has the sentence of its type: `<type>: the translator has no rule for it yet.`
- An order of two variants in a contract, such as `v < w`, has no rule. The sentence is `the contract line has a form the translator cannot read.`
- A variant parameter is an argument for a variant parameter by value, as a copy of the value.
- The core decides that a variant of one type twice has no rule. The sentence of `Refusal::Element` names that case too: `an optional of a struct, a sequence of bool or a variant of one type twice has no rule yet.`
- In the contract language, `static_cast<T>`, `std::get<T>` and `std::holds_alternative<T>` read the type name `T` with one rule.

## Why

C++ lets a variant lose its value when the change to a new alternative throws. Then the variant holds no alternative, and `std::get` throws `std::bad_variant_access`. The model has two states only, so it proves that the read cannot throw. The review showed such a variant with a struct that holds a `std::vector`. libstdc++ never leaves a variant without a value when each alternative is trivially copyable and at most 256 bytes. That is a new trusted assumption: `libstdc++ never leaves a variant of such alternatives without a value.` The ceiling is libstdc++. The upgrade path is a third constructor of the datatype for the state with no value.

Dafny orders two values of a datatype by a rank that C++ does not know, as for an enum, decision 0115. So an order of two variants means something other than in C++. A function that takes a variant by value cannot get one from verified code without the copy. The review showed that a wrong entry in one of the three tables of type names passed every check. One rule for the type name makes them agree.

## What changes

The plugin checks the size and the copy of each alternative, and it reads the copy of a variant argument. It leaves the check of two equal alternatives to the core. The core refuses an order of variants and reads the type name with one rule. The shell gives the new sentence of `Refusal::Element`. The fixtures of 0202 get the new lines, and the plan lists the trusted assumption.

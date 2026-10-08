# 0060: A literal carries its type, a contract reads parameters by place, and methods and variables have two prefixes

Date: 2026-10-08. Status: decided. Amends 0058 and 0059 after an outside review of slice 2.

## Decision

- A literal in code carries the type that the compiler gave it. The core judges that type as it judges the type of a variable. A literal of a type outside the subset, such as `1u`, is refused. A literal in a contract stays an exact integer with no type.
- So each leaf of code carries a type for the core to judge. The leaves are a variable, a literal, both types of a cast, and the signature of a callee. The compiler writes every usual conversion as a cast in the tree. So each operator works on values of types that the core judged.
- A contract line names the parameters of the declaration that it stands on. The plugin writes those names with the line. The core maps each name to the parameter of the definition at the same place. A name that the declaration does not have is no parameter of the contract, even when the definition has it.
- A method is `c_name` and a variable is `v_name`. A parameter with no name is `v_'N`. So a parameter with the name of a function never hides the method.
- A function can take a library proxy by value, such as `std::vector<bool>::reference`. That is a fourth known limit of the gate, in `docs/soundness.md`. The gate's scope stays closed. The translator refuses the containers that make such a proxy.

## Why

The review found three ways to a model that the C++ does not keep. `-1u < 1u` is false in C++, because the negation wraps. With the type gone, the model read `-1 < 1` and proved a false contract. A declaration `subtract(x, y)` with a contract and a definition `subtract(y, x)` swapped the meaning of the names. The contract read them by name, so Dafny proved the swapped contract. A parameter named `helper` in a call to `helper` gave the method and the variable one Dafny name, and Dafny refused the file.

## What changes

The core gains `Expr::Lit` with a type, and a list of names for each contract line. The plugin writes the type of each literal and the names of the declaration of each contract line. The shell gives variables the prefix `v_`.

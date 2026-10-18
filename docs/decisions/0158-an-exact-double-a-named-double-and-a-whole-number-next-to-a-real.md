# 0158: An exact double with no short decimal, a named double constant, and a whole number next to a real

Date: 2026-10-18. Status: decided. Amends 0150 and 0154. The user asked for the rest of the double examples on 2026-10-18.

## Decision

- In code, a literal of type double whose value is not `d / 10^k` of 0150 can be `m / q`. Here `m` and `q` are in 64 bits and `q` is a power of two. The model writes it as `(m.0 / q.0)`. So `0x1p-30` is `(1.0 / 1073741824.0)`. This is a quotient of two literals of the model, so it is exact and it does not round. A literal with neither form stays refused. Its sentence is `a double literal that the model cannot write exactly`.
- A `constexpr` variable of type double at the scope of the file is a named constant, as an integer is in 0106 and 0107. A constant of a namespace or of a class hides it in the same way. In code, the constant is its value, as a literal is. In a contract, it folds to `(m.0 / q.0)` in parentheses, with a minus before a negative value. A double constant with no such form does not fold. In code, its sentence is `a double constant that the model cannot write exactly`.
- In a contract, an integer literal next to a real is a real. That is, it is an operand of a binary operator, and the other operand has a real in it, decision 0154. A minus or parentheses around the literal keep this. A chain is two comparisons, decision 0064, so this is true in a chain too. So `2 * eps` is `2.0 * EPS`, `DBL_MAX / 4` is `MAX / 4.0`, and `|x| <= 1` is `abs(x) <= 1.0`. A folded integer constant is a literal too.
- An integer that is not a literal stays an integer, such as an integer parameter next to a real. So does an operation on integers alone, such as `1 / 2`. Dafny then refuses the line for its types. A conversion between an integer and a double still has no rule.
- A contract cannot write a hexadecimal literal. It names a constant instead.
- The words `eps`, `eta` and `DBL_MAX` of 0154 hide a name of C++. So the translator refuses a contract line that reads one of these words when C++ finds a name with the same spelling from the function. That name can be a parameter, a local, a field or a member of the class. It can also be a constant of a namespace or of the file, or a global variable. The plugin asks C++ which names it finds. The sentence is `eps in the contract is a contract word, and a C++ name too. Rename the C++ name.` A name of the C++ with no contract line that reads the word is no clash.

## Why

The example `double` needs the tolerance `T = 0x1p-30` in code and in its contract. The exact decimal of 2^-30 has 21 digits, so it is not `d / 10^k` with `d` in 64 bits. A power of two below the literal is a better form, because it holds every double from 2^-63 up with all its bits. The example `double_expression` needs `3 * eps` and `DBL_MAX / 4`. A person reads a whole number next to a real as that real. Only a literal changes, so a division of integers keeps the meaning of 0088.

The fold of a double constant gives tokens of 0150 and 0154: two decimals and a `/` that is the real quotient. So the contract needs no new form for it.

The review found that a constant `eps = 5.0` of the file let a false contract prove, because the contract read the word and not the constant. A parameter and a field had the same gap since 0154. The second review found the gap for a static member, a namespace constant and a global variable too, so the check now asks C++ itself. A named double constant makes this name easy to write, so the refusal is part of this decision.

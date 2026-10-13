# 0144: An index name is no field and no constant, and `auto` by value

Date: 2026-10-13. Status: decided. Amends 0143.

## Decision

- The name on an index line must not be a field of the object of the method. It must not be a named constant of the file or an enumerator. The sentence is the one of 0143: `NAME on the index line is a name the function already has.` The core refuses a field. The shell refuses a constant and an enumerator, because the shell folds them before the core sees the line.
- The loop variable of a range-for has a name. A structured binding, as `for (auto [a, b] : v)`, has no rule.
- Two range-fors with no index line each get their own new name, also when they start on one line.
- Decision 0143 names `auto x` as a loop variable. Over a sequence of a scalar, the gate refuses it under the row of plain `int`, because the type is not written. `const auto& x` and `T x` with the type written are in.

## Why

The review of 0143 found each of these. The core read a field on the index line as the index. It read a constant as the constant. So the two cases went opposite ways, and both broke the rule of 0143 that the name is new. Neither gave a proof of something false, because Dafny proved each line as the core read it. Two range-fors on one line shared the new name of the shell. The core then refused the second one with a name that the author never wrote.

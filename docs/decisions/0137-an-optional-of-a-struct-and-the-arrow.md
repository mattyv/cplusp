# 0137: An optional of a plain struct, and `->` on an optional

Date: 2026-10-12. Status: decided. Amends 0075 and 0076.

## Decision

- `std::optional<S>` is in the subset when `S` is a plain struct of the file that holds no sequence. It is a Dafny `Option<S>`, as an optional of a scalar is, decision 0075. It can be a parameter, a local or a result.
- An optional of a struct that holds a sequence stays out, as the struct is a parameter only, decision 0076. The sentence is the one of 0076: `a struct that holds a sequence is in the subset only as a parameter.`
- In code, `o->f` reads the field `f` of the value of `o`. It is `o.value().f`. Dafny proves that the optional holds a value there.
- In a contract, `o->f` is `o.value().f` too. The lexer reads `->` as one token, before `-` and `>`. After `->` comes the name of a field, and any other token refuses the line.
- A write through `->`, such as `o->f = e`, has no rule yet.

## Why

The survey of the examples that do not prove found that `message_header` stops only at `std::optional<Header>`. A parser that gives a header or nothing is the common shape of such a function. The value of an optional is the same value with or without the arrow, so the model of 0029 holds. The check of Dafny on the value is the check of 0075 and 0131.

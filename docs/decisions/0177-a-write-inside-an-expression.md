# 0177: A write inside an expression

Date: 2026-10-24. Status: decided. Builds on 0058, 0104, 0105, 0108 and 0171. The example `evaluation_order` has `return x++;` and `return next(x) > 0 && next(y) > 0;`.

## Decision

`x++`, `x--`, `++x` and `--x` can stand inside an expression, on a local, a reference parameter or a global that the function lists. The write runs before the statement, as a call does under decision 0104. The value of `x++` and `x--` is the value before the write, held in a temporary. The value of `++x` and `--x` is the value after it. The write has the overflow check of an assignment.

A call of a function that writes a value back can stand inside an expression. It runs before the statement, into a temporary, and writes its values back, as a call that stands alone does under decision 0108. A call that gives no value stays alone.

In one expression, at most one write runs where C++ does not fix the order. The translator refuses a statement with two such writes. The sentence is "two writes in one expression. C++ does not fix the order." The translator refuses a statement that writes a name and also reads that name elsewhere in the expression. The sentence is "x has a write and a read in one expression. C++ does not fix the order." The gate row `evaluation_order` refuses both forms too. The translator checks them as well, so the model never rests on the gate alone. A write in the condition of a `while` or a `for` loop has no rule. The sentence is "a write in the condition of a loop: the translator has no rule for it yet."

The right side of `&&` and of `||` and a branch of `?:` run only when C++ runs them. A `return` whose value holds a call or a write in such a place becomes an `if`. `return a && b;` with a call in `b` is `t := a; if t { t := b }; return t;`. For `||` the branch runs when `t` is false. For `c ? a : b` each branch gives `t` its value. A call with no write in such a place takes the same path, which lifts the refusal of decision 0104 for it. A call in the condition of a `while` or a `for` loop keeps its refusal. So does a write there. In any other statement, a call or a write in such a place keeps the refusal of decision 0104 too. The lowered `return` is one statement of the model, so each line keeps its place. A `return` of `!` or of arithmetic around such an `&&`, `||` or `?:` keeps the refusal too.

A compound assignment such as `x += 2` as a value has no rule yet. It keeps the sentence of today.

## Why

The example `evaluation_order` has one change of state in each full expression, and a pair that the standard orders. Decision 0104 lifts a call that changes nothing to a temporary. A write is the same thing with a value written back. One write among reads of other names runs in the order of the statement. Two writes, or a write and a read of the same name, have no order in C++, and the gate refuses them. The translator refuses them too, so a file that passes the gate by a gap still gets no model. The `if` for `&&` is exactly what C++ does: the right side runs after the left and only when the left is true.

## What changes

The core gains `Expr::Step` for a write inside an expression. It gains two kinds of lifted statement: a write into a temporary, and a call that writes back into a temporary. It lowers a statement with a call or a write under `&&`, `||` or `?:` into an `if` with a temporary. It gains the three refusals, with the check of the two order refusals before a statement translates. The plugin writes `++` and `--` inside an expression as `Step` with the name, the type, the direction and whether it is a prefix. The shell prints the two kinds and the refusals. Three fixtures: `model-writes.cpp` proves, `model-writes-wrong.cpp` fails at the named lines, `model-writes-refuse.cpp` refuses with the sentences. The example `evaluation_order` proves. Three lines of `model-lift-refuse.cpp` said "a call out of place" for a call on the right of `&&` or `||` or in a branch of `?:`. They now have a model, and the test keeps its two loop lines. The line of `model-cond-refuse.cpp` for a call in a branch of `?:` has a model too. The sentence of decision 0104 loses the words about a call that writes a value back. It is now "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone."

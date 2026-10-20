# 0167: A lemma for the bound of a product, and apply lines in a pure member function

Date: 2026-10-20. Status: decided. Amends 0090, 0099 and 0165.

## Decision

- The prelude of the model has the lemma `MulBound(a, b, c, d)`. It requires `0 <= a <= c` and `0 <= b <= d`, and it ensures `0 <= a * b <= c * d`. Dafny proves it from a lemma `MulNonneg` of the prelude, so it adds no axiom.
- An apply line can call `MulBound`, as it calls a lemma of the companion file, decision 0099. An example is `//@ apply MulBound(x, k_, 1000, 1000)` above `return x * k_;`.
- A pure member function of 0090 can have apply lines above its `return`. Its function in the model calls each lemma before its value, as `L(a); e`. The method calls each lemma before its `return`, as 0099 says.
- The check of an override, decision 0165, calls the lemmas of the override in its body. The arguments read the parameters and the object of the override.
- `prove` reports a failure of an apply line in a pure member function once, at the apply line. The function and the check repeat the call of the method.
- The check of an override reads its lemmas under the requires lines of the interface. A lemma that holds in the method and fails in the check shows that the override requires more than the interface. `prove` then says `the override may require more than B::f.` with the requires line of the override.
- An assert line above the return of a pure member function has no rule yet.
- The companion file cannot declare `MulBound` or `MulNonneg`, decision 0083.
- The examples `strategy`, `decorator`, `factory` and `shape_area_sum` get an apply line above each product of two names.

## Why

Dafny reads a product of two names with a solver that guesses. The same bound proves in one run and fails in another, and `0 <= x * k && x * k <= 1000000` fails where each half alone proves. The lemma gives the bound as a fact, so the proof no longer depends on the guess. With the lemma, a hand model of `strategy` proves in every run that we tried, also with each assertion on its own. The lemma names its bounds, because the translator cannot know them. The bot writes the bounds from the requires lines. A sentence that tells the bot to add the line is the upgrade path.

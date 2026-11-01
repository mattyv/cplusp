# 0225: Fixes from the pre-review

Date: 2026-11-01. Status: decided. Amends 0068, 0174, 0177, 0178, 0209, 0215 and 0216. A review of the whole code found these defects before an outside review. Each has a fixture.

## Decision

- `prove` uses the Dafny that `DAFNY` names. When it does not run, `prove` stops with exit 2 and names the path. No other Dafny takes its place.
- `prove` refuses `--time-limit 0`, because Dafny reads 0 as no limit.
- A pointer to a global inside an object is a change of the global for the state check. This holds when a team loosens `raw_pointer`.
- A qualified call of a static member function in a contract of a member function takes no object.
- A contract can name a static member function by its class inside a namespace.
- Take a bare call in a contract of a member function, of a name that two member functions share. It gets the sentence of a function that is not pure.
- A conditional of two locals with destructors is a copy. So the core refuses a return of it, as it refuses a return of one local.
- A `const` virtual function that gives a value and writes a parameter has no rule yet. The sentence is `a const virtual function that gives a value and writes a parameter: the translator has no rule for it yet.`
- An assignment of a call that writes its object has a rule in each spelling, also alone: `x = c.bump();`.
- A braced list in a bare block gets the sentence of a braced list.

## Why

Each case gave a wrong result. Some proved when the core must refuse them, some got the wrong sentence, and some gave a Dafny error with no sentence. An outside reviewer can find each one in minutes. The rule in each fix is the rule that the decision of the case already states.

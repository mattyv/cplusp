# 0155: Each refusal names its own cause

Date: 2026-10-18. Status: decided. Amends 0108, 0124, 0149, 0150 and 0154. The reviews of 0148 to 0154 found these sentences.

## Decision

- A requires line that the translator cannot read gets its own refusal. The check of `std::isfinite` of 0150 does not run while such a line is in the contract, so its sentence does not hide the real cause.
- An expression is of type double only when its value is. A conversion to an integer is not, so `static_cast<int32_t>(x) % 2` gets the sentence of the conversion, not the sentence of a rounding.
- A decimal with more than 19 digits after the point gets the sentence `a decimal with more than 19 digits after the point`.
- A reference parameter or a double parameter with no name gets a sentence that tells the author to name it. The sentences are `a reference parameter has no name. Give it a name and put it on the modifies line.` and `a double parameter has no name. Give it a name and say std::isfinite of it in a requires line.`
- `prove` prints each failure once. Dafny can report one check twice, for example the condition of a loop at its start and after a turn.
- The plugin takes `std::count_if` only from a system header. A function of that name in the file itself stays a call with no model.

## Why

Each of these sentences named a cause that the author could not fix, or no cause at all. The bot reads the sentence and acts on it. So a wrong sentence costs a turn, and it can make the bot write the same line again.

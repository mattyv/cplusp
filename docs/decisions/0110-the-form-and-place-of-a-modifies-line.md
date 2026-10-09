# 0110: The form and the place of a modifies line

Date: 2026-10-09. Status: decided. Amends 0108.

## Decision

- A modifies line is a list of names with a comma between each two. A name can have parts with `::` between them, as in `Tally::count_`. The translator refuses each name that is no reference parameter of the function, as 0108 says.
- A modifies line that has any other form is refused at its line with the sentence of a form the translator cannot read. This refusal comes before the check that each reference parameter is on the line.
- A modifies line goes above a function. The sentence of a contract line in the wrong place now names it: `A requires, an ensures, a modifies or a decreases line goes above a function.`

## Why

The review of the 0108 shell found two wrong sentences. A line such as `modifies x,` said that the line did not name `x`, which it does. A name with `::`, which the gate reads as a global, got the sentence of a bad form, not the sentence of 0108. The bot reads each sentence, so each one must name the true fault.

# 0103: What a trusted function promises

Date: 2026-10-09. Status: decided. Amends 0102, from the review of its green step.

## Decision

- A trusted function promises its contract and one more thing. It changes no parameter that it takes by value, by a const reference or by a span of const. It changes its object only when it is not const. The model takes each such parameter as a value, so a proof of a caller rests on this promise. A trusted body that writes such a parameter, for example through `const_cast`, breaks its promise. The `Trusted:` line names the function, so a reader checks this promise as part of its contract.
- The reason of a marker is one line. The gate refuses a reason that holds a line break or another control character: `NAME has a reason with a line break. A reason is one line.` So no reason can put a false line into the report.
- The `//@` lines in the body of a trusted function belong to that body. The translator does not read them, as it does not read the body.
- The `Trusted:` lines come first in the report, before each `Not provable:` and each `Not proved:` line.
- When a trusted function has a marked declaration and a definition, the `Trusted:` line names the line of the marked declaration. The contract of the function is the contract lines of all its declarations together.

## Why

The review found a trusted function that wrote a field of a const reference argument. Its contract was true, and the caller proved a false result from the model, which holds that argument as a value. The review also found a reason with a line break that printed `ok: proved` on a run that failed. And it found a trusted body whose loop invariant the translator refused as a line of no function.

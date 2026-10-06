# 0036: An analysis that cannot finish refuses

Date: 2026-10-06. Status: decided. Follows a fourth outside review and a second inside review of the round of decisions 0032 to 0035. Amends 0032, 0033 and 0035 where each skipped what it could not see.

## Decision

A check that cannot finish its analysis of a function refuses the function. It never reports the function as clean. Four rules follow from that.

- **Templates are judged where they are used.** The semantic checks run on every instantiation in the translation unit. There every type and every callee is known. They do not judge the dependent pattern. The allowlist still judges the pattern's kinds. The aliasing check, the const-handle check, the sequencing check and the state check share this rule.
- **A callee the check cannot read changes state.** A call changes state when its callee has a mutable parameter or is a non-const method. It changes state when its callee has a name on its `modifies` line, or writes a global in its body. A function outside std may have no body in this translation unit and no contract lines. A call to it may do any of these. So it counts as a change of state that may reach any global.
- **No budget ends in a pass.** A walk over an object graph, a call graph or a type follows it to the end. If a walk must stop at a limit, the function is refused with a finding that says so.
- **The compiler reads the source.** The gate finds a line directive with the compiler's own raw lexer, not a scanner of its own. The lexer knows raw strings, comments, digraphs and splices, because it is the one that reads them for the build.

## Why

The fourth outside review found four ways past the round, and the second inside review seven more. Every one had the same shape: an analysis that did not finish, and a result of "no effects" in its place. A template body whose callee was unresolved. A function with no mutable parameters, assumed to change nothing. A destructor nine structs deep, past a depth limit. A raw string that a hand scanner read as a comment. An allowlist proves only that every node has an allowed kind. It does not prove that every check understood every node. Only a check that refuses what it did not finish closes that gap.

## What changes

The four rules in the plugin and the gate, with a banned line or fixture for each review finding. The kinds a row claims go back to the row, and the lists carry them too. A team that loosens a row allows its kinds. A team that loosens `unlisted` keeps every ban. The soundness map says what each check reads, and where it stops.

# 0056: The translator is the gate, and its decisions are proved

Date: 2026-10-08. Status: decided. Builds on 0032, which made the gate an allowlist. Supersedes the plan's separate gate and translator when the translator covers the examples.

## Decision

- The translator from C++ to Dafny is the gate. It accepts only the C++ that it can turn into a faithful model, and it refuses everything else. "Allowed" means "the translator handled it". No separate list of bans stays.
- The project keeps as much of its code in Verus as it can. Each decision of the translator lives in the Verus core. The trusted edges do only what Verus cannot reach, and each new piece of logic starts in the core.
- The work splits in three:
  - The clang plugin is a thin trusted edge. It walks the compiler's tree and writes the subset as data. The data holds the nodes, their types, and the calls that the compiler resolved. It holds the lowered form of decision 0037 where a check needs it. The plugin decides nothing.
  - The core, in Verus, reads that data and gives a model or a refusal. Its proofs say that each node is translated or refused, and that an unknown node is refused. They say that no node is skipped, and that each construct takes the rule of its battery case.
  - The shell renders the model as Dafny text and runs Dafny. Text rendering is a trusted edge already.
- The core cannot prove that the model means what the C++ means, because C++ has no formal semantics to prove against. The divergence battery and the differential run stay the evidence for that.

## Why

Two programs each read C++: the plugin judges what is allowed, and a translator would turn it into a model. Each hole that a review found was a place where the plugin passed what the model would read another way. Seven outside reviews and many inside reviews found them, one family after another. One reader removes the gap between the two. The plugin also grew to 3734 lines of unproved C++ beside 1096 lines of proved core. CLAUDE.md says that the trusted edges stay thin. This turns that around.

## What changes

The first slice is the case `radix_find`. The plugin writes its tree as data, the core translates it, and Dafny must prove the result as it proves the hand-written model. The current plugin stays as a second gate until the translator covers the examples. Then each check whose work the translator does goes. The gate's scope stays closed in the meantime, decision 0055 and docs/soundness.md gap 2.

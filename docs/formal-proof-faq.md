# Formal proof FAQ

For C+P. Evidence and guidance checked on 8 October 2026.

## What does a formal proof establish?

It establishes that a program or model satisfies specified properties under stated assumptions.
For example, a search returns the correct position for every input allowed by its contract.
The guarantee depends on the verification tools and the interpretation of the program.

## Does it cover every input?

A deductive proof can cover every input allowed by the contract.
Testing checks executions that actually run.
Bounded verification covers its specified bounds.
Always report which method and bounds a result uses.

## Does a proof mean the program does what I wanted?

Only if the specification captures what you wanted.
A sort that returns an empty array satisfies a requirement that the output is ordered.
It violates the additional requirement that the output preserves all input elements.
Review the specification for missing behavior.

## Can agents write the specifications?

Yes, but quality varies with the task.
The research report describes strong results on small tasks and weaker results on repository requirements.
Review agent-written specifications against requirements and independent examples.
The prover checks the implementation against the specification.
It does not automatically establish that the specification captures your intent.

## Can small proofs combine into a whole-program proof?

Yes, when callers establish callee preconditions and callee guarantees establish the caller's required result.
Include state effects, initialization and interactions between components.
Verify all relevant implementations.
A collection of locally correct helpers can still implement the wrong overall algorithm.

## Does keeping functions small solve the problem?

Small components can make proof tasks easier.
Choose boundaries that expose useful, stable guarantees.
Contracts and abstractions determine how much reasoning callers can reuse.
The report's experiments support decomposition workflows.
They do not establish an ideal function length.

## Can proofs establish that a program cannot crash?

They can establish absence of specified run-time errors within the analysed scope.
Examples include bounds failures, invalid arithmetic and failed assertions.
Hardware faults, operating-system failures and exhausted resources need separate treatment.
A proof of termination does not establish that the target has enough stack or memory.

## Can proofs establish termination or performance?

They can establish termination with appropriate loop or recursion measures.
Specialised proofs can establish operation counts or resource bounds.
Ordinary functional proofs do not establish latency, throughput or real-time deadlines.
Hardware timing and scheduling need additional models or measurements.

## Do proofs cover concurrency?

Only when the model and proof rules cover relevant thread interactions.
Sequential proofs alone do not establish correctness under concurrent interference.
Atomics, ordering and shared state need explicit treatment.
C+P's current sequential translation is not a general concurrency proof.

## Why does C+P need translation checks?

C+P proves a Dafny model of C++.
A faithful translation must preserve arithmetic, control flow, state changes and the relevant lifetime and aliasing rules.
A successful Dafny proof does not establish behavior that the translation omitted or changed.
The translator must refuse constructs it cannot model.

## What remains trusted?

Requirements, external-code contracts, verification tools, translation and compilation can introduce assumptions.
The target and execution environment can introduce more.
Record these assumptions.
Use proof, review or testing to justify them where possible.
A bodyless trusted method provides a promise, not a proof of its external implementation.

## Can a proof pass for the wrong reason?

Yes.
Contradictory assumptions can make a proof vacuous.
An excessively restrictive precondition can remove valid use cases.
A weak postcondition can omit the required behavior.
Skipped code can leave a dependency unverified.
Review these cases.
Use assumption audits and consistency checks, while recognising their limits.

## Do proofs replace tests and reviews?

They can replace tests for properties fully established by the proof within its scope.
Keep independent evidence for requirements, integration, external code and executable behavior.
For C+P, tests also help detect differences between C++ execution and its Dafny model.

## What happens when the code changes?

Re-run the relevant proofs and validate the translation.
A replacement that preserves a component contract can preserve callers' reasoning.
A changed contract can affect every caller that relies on it.
Record the source revision, proof settings, scope and remaining assumptions.

## What should a proof result tell me?

- The property proved.
- The source revision and analysed scope.
- The input restrictions and any verification bounds.
- The trusted dependencies and target assumptions.
- The unproved obligations or excluded code.
- The independent evidence about the executable.

## Where can I read the evidence?

- [Research report](research/formal-verification-llm-coding-report.md): measured results, decomposition and limits.
- [Dafny reference manual](https://dafny.org/latest/DafnyRef/DafnyRef.html): contracts, complete verification and assumption audits.
- [SPARK contracts](https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_write_subprogram_contracts.html): functional correctness and contract consistency.
- [SPARK assumption management](https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_use_gnatprove_in_a_team.html): unverified dependencies and trusted assumptions.
- [Iris](https://iris-project.org/): reasoning about concurrent programs.

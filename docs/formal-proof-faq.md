# Formal proof FAQ

For C+P. Evidence and guidance checked on 8 October 2026.

For build and command instructions, read [Use cplusp](getting-started.md).
For the project's specific assumptions and gaps, read [soundness](soundness.md).
This FAQ explains how to interpret proof claims.

## What does a formal proof establish?

It establishes that a program or model satisfies specified properties under stated assumptions.
For example, a search returns the correct position for every input allowed by its contract.
The guarantee depends on the verification tools and the interpretation of the program.

## Does it cover every input?

A deductive proof can cover every input allowed by the contract.
Testing checks executions that actually run.
Bounded verification covers its specified bounds.
Always report which method and bounds a result uses.

**Example:** a binary-search proof may cover every sorted input sequence.
It says nothing about searching `[3, 1, 2]`, because that input breaks the sorting precondition.
A check limited to sequences of length 10 also says nothing about length 11.

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

**Example:** sort an input, then search for `7`.
The sort must preserve the elements, and its ordering guarantee must satisfy the search's precondition.
Together, those contracts let you prove whether `7` occurred in the original input.
If sorting can discard elements, that final conclusion does not follow.

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

**Example:** a loop with one billion iterations can have a valid termination proof.
That proof does not establish a one-millisecond deadline.

## Do proofs cover concurrency?

Only when the model and proof rules cover relevant thread interactions.
Sequential proofs alone do not establish correctness under concurrent interference.
Atomics, ordering and shared state need explicit treatment.
C+P's current sequential translation is not a general concurrency proof.

**Example:** two threads each read an atomic counter as `0`, then each store `1`.
Each follows its own read-then-increment logic, but the final count loses one increment.
A sequential proof does not exclude this interleaving.

## Why does C+P need translation checks?

C+P proves a Dafny model of C++.
A faithful translation must preserve arithmetic, control flow, state changes and the relevant lifetime and aliasing rules.
A successful Dafny proof does not establish behavior that the translation omitted or changed.
The translator must refuse constructs it cannot model.

**Example:** incrementing a C++ `uint32_t` holding `4294967295` produces `0`.
An unbounded Dafny `int` instead becomes `4294967296`.
Proving that this integer increases would establish the wrong claim about the C++ operation.
The model must represent wrapping, or the verified input range must exclude it.
This illustrates the obligation, not a claim that C+P currently permits wrapping.

## What remains trusted?

Requirements, external-code contracts, verification tools, translation and compilation can introduce assumptions.
The target and execution environment can introduce more.
Record these assumptions.
Use proof, review or testing to justify them where possible.
A bodyless trusted method provides a promise, not a proof of its external implementation.

## Can a proof pass for the wrong reason?

Yes. A verifier can correctly prove a claim that gives you less than you think.
These examples use simplified contract notation.

| What went wrong | Concrete example | Why the proof can pass | What to check |
|---|---|---|---|
| Impossible inputs | Require both `x > 0` and `x < 0`. Promise any result. | No integer satisfies the requirements. There is no allowed execution that could violate the promise. | Show that intended inputs satisfy the preconditions. |
| Valid cases excluded | An absolute-value function returns `x`, but requires `x >= 0`. | It is correct on nonnegative inputs. The contract excludes every negative input. | Check whether the requirement includes cases such as `abs(-5) == 5`. |
| Result too weak | Promise only `result >= 0`. Implement absolute value by always returning `0`. | Zero is nonnegative, even when the required answer is `5`. | Specify the required relation between input and output. |
| Answer assumed | Assume `result == x + 1`, then prove that same statement. | The proof starts by accepting the fact it was meant to establish. | Derive the fact from verified code. Audit added assumptions. |
| Dependency unproved | Trust that an external index function returns `0 <= i < length`. Its actual code can return `length`. | The caller's proof uses the promised bound without checking the external body. | Verify the dependency, or report and independently check the trusted promise. |

The first case is a **vacuous proof**: no input meets the conditions, so the guarantee has no applicable case.
A verified caller would also have to establish those impossible conditions before calling the function.
The proof does not make an invalid call safe.

**A useful review question:** could an obviously wrong implementation still satisfy this contract?
For sorting, try returning an empty sequence.
For absolute value, try returning zero.
For a state update, try doing nothing.
If an implementation that violates the requirement still verifies, a required condition is missing or an assumption is too strong.
These checks can expose gaps. Passing them does not prove that the specification is complete.

## Do proofs replace tests and reviews?

They can replace tests for properties fully established by the proof within its scope.
Keep independent evidence for requirements, integration, external code and executable behavior.
For C+P, tests also help detect differences between C++ execution and its Dafny model.

## What happens when the code changes?

Re-run the relevant proofs and validate the translation.
A replacement that preserves a component contract can preserve callers' reasoning.
A changed contract can affect every caller that relies on it.
Record the source revision, proof settings, scope and remaining assumptions.

**Example:** replacing one sorting algorithm with another can preserve the sort-then-search proof.
Both must establish the same ordering and element-preservation guarantees.
Changing the contract to allow dropped duplicates requires review of callers that depend on their count.

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

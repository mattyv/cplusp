# C+P end-to-end validation plan

Date: 2026-10-09. Status: planned. Tests application scale and the skill's complete development process, as in decisions 0092 and 0093.
It does not record completed program runs. The runs so far are the larger examples under `examples/` and the trial in `docs/trial-flashradixtree.md`.
Capability review: commit `7bbdc9201eebc9eb23b43900f1f1a7b8361a5aea`.

## What we are testing

Test the complete path from a program requirement to a working executable:

1. Start with an application brief. Use the skill to derive requirements, module boundaries, state invariants and candidate formal contracts.
   Review them before implementation. Do not supply a finished specification for this process test.
2. Have the coding agent implement the C++.
3. Run the public `cplusp prove` command on the source.
4. Check the gate, automatic translation, proof result and C++ diagnostic locations.
5. Have the agent use the diagnostics to repair the implementation or supporting proof annotations.
6. Compile and run the C++ against independent tests and a reference implementation.
7. Change the program and repeat the complete path.

The unit under test is C+P and its coding workflow.
A hand-written Dafny model that verifies does not count as an end-to-end pass.
A successful `cplusp model` command does not count as a proof.
Use companion specification definitions where the current translator permits them.
Keep the generated model unchanged during acceptance runs.

## Test the skill as a development process

Test whether the [project skill](../skills/cplusp-dafny/SKILL.md) works as a repeatable method for building and maintaining applications.
Successful verifier runs alone do not establish that the method works.
The agent must produce the required application, follow the process and expose unfinished obligations accurately.

Start each application with a reviewed plain-language brief, normal repository context and a fixed resource budget.
Let the agents generate the specifications and decomposition using the skill and the repository's coder/reviewer roles.
Keep independent acceptance tests and evaluation mutations separate from development feedback.
Record the skill revision with the source and tool revisions.

| Process step | Required output | What to assess |
|---|---|---|
| Recover requirements | Requirement list, input domain, failures and evidence of intent | Missing behavior, invented requirements, unresolved ambiguity and excluded valid inputs |
| Decompose and specify | Module boundaries, state invariants, component contracts and early composition checks | Whether contracts suffice for the application requirement and whether the chosen boundaries make proofs manageable |
| Review specifications and write tests | Reviewed contracts, admissible-input checks, independent examples and failing development tests | Whether review catches weak or conflicting contracts before implementation relies on them |
| Implement and prove incrementally | Working increments, verifier logs and an explicit list of open helper obligations | Proof-repair loops, premature dependence on unproved helpers, contract weakening and human assistance |
| Integrate the application | Initialization proofs, checked callers, closed core obligations and a complete executable | Local proofs that fail to establish a system guarantee, missing bodies and unexpected trusted dependencies |
| Challenge and review | Fixed-contract mutations, concrete witnesses, classified outcomes and a requirement coverage check | Wrong implementations that still verify, missed requirements and inaccurate claims of completeness |
| Maintain and hand off | A feature change, a contract change, a regression fix and a saved record of obligations | Whether the process remains usable after changes and whether another agent can continue from ordinary repository artifacts |

Run the complete process at every application size.
Do not hand the agent a ready-made module decomposition and then claim the skill produced it.
Where a stage reuses earlier components, give comparison runs the same starting snapshot and record the inherited contracts.
Use the existing-code workflow when the task changes or extends an earlier application.

Record where the method breaks: specification, decomposition, tool support, proof repair, integration, review or maintenance.
An appropriate report of an unsupported construct is correct process behavior, but the application remains blocked.
Separate that result from an agent ignoring the skill or falsely claiming completion.

Count all specification work, reviewer effort, failed attempts and interventions in the total cost.
Record every requirement or contract correction and its effect on implementation and proofs.
Distinguish the ordinary planned review from extra assistance needed to finish the task.
If a person supplies a missing invariant, specification or design, record that assistance.

For a successful process run, the application must meet independent acceptance checks within the recorded budget.
The required core proofs must close, and the report must state the actual scope and assumptions.
An assisted success, blocked run or exhausted budget is a separate result.
Record conformance to the skill and application success separately. Following the steps does not guarantee the right result.

Pin the skill during a measured batch. Improve it between batches using the recorded failures.
Re-run held-out tasks with the revised skill. Do not evaluate an improvement only on the example that prompted it.

## Programs and order

Build executable applications, with several modules from stage 2 onward.
Increase source size, module count and the amount of behavior that must compose.
Keep file and console I/O outside the verified core and name that boundary.

The size bands estimate executable C++ for the complete application, excluding comments, specifications, tests and generated code.
Record the verified core's size separately. A large trusted shell does not exercise proof scalability.
These are planning estimates. Use useful behavior to create scale. Do not pad the source to meet a number.
If an application is substantially smaller, report the smaller scale actually tested.

| Order | Application | Planned source scale | Concrete scope | What the stage tests |
|---|---|---:|---|---|
| 1 | **Toy arithmetic program** | 50–100 lines | Clamp, checked addition and a tiny executable driver | Confirm the complete source, proof, diagnostic and repair path |
| 2 | **CLI telemetry analyzer** | 500–1,000 | Read numeric records, validate fields, filter by time and ID, calculate count/sum/min/max, and answer range queries | Several cooperating parsers and algorithms, complete CLI behavior, many caller proofs |
| 3 | **Inventory and order-management application** | 2,000–4,000 | Products, stock receipts, reservations, order placement, cancellation, fulfilment, reports and command replay | Mutable collections, several linked state machines, atomic rejection and cross-module invariants |
| 4 | **Persistent indexed key-value store** | 5,000–10,000 | Byte keys, put/get/delete, prefix scans, a radix index, append-only journal, reload and compaction | Recursive mutation, indexing, logical persistence and preservation of observable contents across maintenance |
| 5 | **Matching-engine application** | 10,000–20,000 | Single-instrument limit orders, cancel, amend, partial fills, price/time priority, trades, depth queries, snapshots and replay | Large interacting invariants, ordered state, rich command behavior and maintained proofs across changes |
| 6 | **Single-process exchange simulator** | 20,000–40,000 | Multiple instruments and accounts, risk checks, funds/position reservations, matching, settlement, journal replay and queries | System-scale composition, independent subsystem proofs, consistency across subsystems and incremental verification |

Stages 1 and 2 establish that the end-to-end workflow is usable.
Stages 3 and 4 test applications with thousands of lines and meaningful state.
Stages 5 and 6 test larger systems with many contracts and dependencies.
Each stage gets a runnable application and a recorded proof scope.

Reuse parsers, checked arithmetic, byte-frame decoding, queue operations and lookup algorithms as components of these applications.
The small programs from the original ladder remain feature probes and regression cases.
They no longer constitute the application-scale milestones.
Reuse useful verified components between stages and measure the cost of adapting their contracts.

### Required guarantees by application

| Application | Requirements the composed proof must establish |
|---|---|
| Telemetry analyzer | Accept and reject records according to the declared grammar and numeric limits. Return statistics for exactly the selected records. Handle empty selections explicitly. |
| Inventory and orders | Reservations never exceed available stock. Placement, cancellation and fulfilment preserve the stock accounting identities. Rejected operations change nothing. Order and inventory views agree. |
| Key-value store | Reads reflect the last successful write or deletion. Prefix scans return exactly the matching live keys. Replay reconstructs the logical contents. Compaction preserves every observable key/value result. |
| Matching engine | Matches obey price/time priority. Trades and resting quantities account for accepted quantity. Cancellation and amendment affect the named live order only. Snapshot plus replay matches uninterrupted execution. |
| Exchange simulator | Accepted commands meet the risk policy. Reservations cover obligations under the stated model. Trades produce the defined debits, credits and position changes. Journal replay reproduces the composed state. |

For persistence, prove the logical encode/decode, replay and compaction behavior over bytes and records.
Specify the assumptions about successful file reads and writes separately.
Do not claim crash durability or operating-system correctness from those logical proofs.
Report proof coverage of the application's core separately from executable tests of its I/O.

### Scope choices before implementation

- Keep the first campaign single-threaded. Concurrency needs a separate campaign and proof scope.
- Use fixed-width integer prices, quantities and balances. Avoid floating point in the first financial applications.
- Give collections explicit capacity rules. Make capacity exhaustion an observable result.
- Review all ID reuse, duplicate input, cancellation, amendment and partial-failure rules before coding.
- State whether amendment preserves or loses time priority.
- Define arrival sequence exhaustion and a full book's treatment of a partially matched incoming order.
- For replay, define the first-error policy, trailing incomplete record behavior and exact command-consumption rule.
- Do not turn invalid external input into a precondition that the program never checks.

## Use the current slice honestly

This is a target scale ladder, not a claim that the present translator supports all six applications.
Existing examples often pair C++ with hand-written Dafny.
Reuse their requirements and fixtures, but qualify them through automatic translation.
Run small feature probes before building each application.

| Checkpoint | Current evidence and required next check |
|---|---|
| Arithmetic and read-only processing | Fixtures cover branches, loops, scalar optionals, read-only sequences, calls and quantified contracts. Prove the exact parser/result types used in stages 1 and 2. |
| Mutation and initialization | Member support is arriving in steps. Read-only sequences do not establish sequence-write support. Prove translation rules for the constructors, collection writes and state effects needed from stage 3 onward. |
| Recursive indexing | The radix lookup slice is reported as proved end to end. Reproduce it and then qualify insertion, deletion and index invariants before building the store. |
| Multiple files and changed contracts | The current CLI proves one source file per invocation. Track every relevant body, dependency contract and affected caller. Establish a reproducible whole-application run. |
| Application scale | Measure full verification and verification after edits at every stage. Track wall time, memory, solver timeouts, diagnostic usability and missing coverage. |

Relevant sources: [examples](../examples/README.md), decisions
[0074](decisions/0074-a-mutable-reference-to-a-struct-has-no-rule-yet.md),
[0076](decisions/0076-structs-that-hold-sequences-and-recursive-structs.md),
[0089](decisions/0089-member-functions-in-steps.md),
[0090](decisions/0090-a-pure-const-member-function-is-also-a-dafny-function.md),
the [CLI](../crates/cplusp/src/main.rs), and the [radix trial](trial-flashradixtree.md).
Recheck the latest decisions before each stage because the slice is changing.

A required construct that lacks a rule blocks that stage.
Record the smallest source that exposes it and implement that capability as a separate change.
Retain the application requirement. Do not mark its central algorithms trusted to obtain a pass.
Refactoring is acceptable when the reviewed behavior stays the same. Record its cost.

## The experiment for every program

Keep a reviewed requirement and a full functional contract for each public operation.
Use the [existing-code workflow](../skills/cplusp-dafny/references/specification-review.md) when adapting an existing example.
Freeze the requirements and contracts during each implementation or repair attempt.
The reviewer decides contract corrections, then restarts the affected attempt with the correction recorded.

Run these cases through the public CLI and the compiled executable:

| Case | Required outcome |
|---|---|
| Correct implementation | The gate accepts, automatic translation finishes, and all required bodies prove. Independent executable tests agree. |
| Wrong implementation with fixed contracts | C+P must not report success. Record the failed obligation and its source location. Confirm a requirement violation with an executable witness. |
| Contract missing an essential guarantee | The separate specification review must report the omission. A prover pass is possible and is not by itself a prover defect. |
| Unsupported construct | C+P refuses it with an actionable source diagnostic. Count this as a coverage limit, not a proof rejection. |
| Agent repair | Give the agent the ordinary requirement and diagnostics. It repairs the code or supporting annotations under fixed contracts, then passes independent tests. |
| Subsequent change | Modify a helper, a contract or a boundary condition. Re-run affected bodies and callers and check the composed requirement. |

Select wrong implementations by requirement, with at least one for each distinct required behavior.
Examples: skip the last element, accept overflow, drop duplicates, swap byte order, overwrite a full queue,
debit without credit, cancel the wrong order, or match a later order first.
Give each one an allowed input and an expected wrong outcome before running the prover.
Keep a separate set of mutations and inputs hidden from the agent for evaluation.

Only a completed proof rejection with a relevant obligation counts as detecting the intended defect.
A timeout, syntax failure, translation refusal or tool crash is a separate outcome.
Any wrong executable that receives a successful proof verdict needs investigation before advancing.
First distinguish a missing requirement, a false trusted assumption and a translation or result-handling defect.

### Command path

Use the actual CLI, with the plugin and compiler flags pinned for the run:

```sh
cplusp prove path/to/core.cpp --plugin path/to/libcplusp.so --time-limit 20 -- -std=c++23 -ffp-contract=off
```

Record the full command, policy, source revision, tool versions, stdout, stderr and exit code.
The command above is a template from the current interface, not a report of a completed run.
Compile the same C++ and run the independent oracle checks.
Use sanitizer runs where applicable as additional execution evidence.
Prover success and executable agreement are separate acceptance checks.
Where runnable generated models are supported, compare their output with C++ on the same inputs too.
That comparison supplements the independent oracle and does not prove translation correctness.

Exercise the existing prover-process regressions in the campaign as well.
A missing tool, nonzero exit, timeout, malformed summary or incomplete run must never become a success verdict.
Reuse the existing fixtures instead of copying them into every program.

## When a stage is complete

- All required bodies prove through automatic translation. List every trusted dependency and unproved obligation.
- Independent executable checks cover success, failure, empty input and relevant boundaries.
- All selected wrong variants receive a reviewed classification. No unexplained false success remains.
- The agent completes at least one seeded repair under the recorded budget, or the stage records an agent-workflow failure.
- A subsequent change passes the same checks, including callers affected by changed contracts.
- A clean run from the pinned inputs reproduces the outcome.

A correct refusal validates the refusal path, but does not complete the intended program stage.
Do not advance the dependent stage until the blocking capability or defect is resolved.
Independent stages may continue while the blocker is recorded.

## Measure results without mixing them

Keep one row per attempt:

| Program and revision | Scenario | Translation | Proof | Executable checks | Agent calls and time | Human intervention | Open gap |
|---|---|---|---|---|---|---|---|
| Identify source and tool versions | Correct, mutant, repair or change | Accepted or reason refused | Passed, rejected, timeout or tool failure | Oracle and boundary results | Include proof and specification work | Record corrections and assistance | Name remaining obligations |

Report support coverage, false successes, false refusals, repair success and total cost separately.
Track functional requirement coverage. A count of proved functions alone is insufficient.
Also report total and verified executable lines, modules, functions, dependency edges and remaining trusted code.
Measure a full run, a body-only edit, a contract edit and a shared type change.
Record which callers were rechecked, total resources used and whether previously established guarantees still hold.
Record the ordinary executable build and run cost separately from verification cost.

First establish that the full process works. Then compare two different questions:

- **Does the whole skill process improve app development?** Give both arms the same application brief, starting code, model, reviewer availability and total budget.
  One uses the ordinary coding-and-testing process. The other uses the full skill and C+P process, including specification generation and review.
  Count all authoring, review and proof costs. This comparison measures the whole process and does not isolate the prover's effect.
- **Does proof feedback add value once contracts exist?** Give both arms the same reviewed requirements, contracts and budget.
  One uses tests. The other also receives C+P feedback. This holds specification information constant.

Judge both comparisons with the same independent executable tests and requirement review.
Repeat with independent attempts. A few initial runs are a pilot, not a reliable effect estimate.

## First execution batch

1. Build the campaign around stage 1 and one intentional arithmetic error.
2. Confirm the entire source-to-diagnostic-to-repair-to-executable path.
3. Build stage 2 as the first application with several cooperating modules.
4. Fix workflow defects and qualify mutation support before starting stage 3.
5. Continue through the application size bands, adding only the capabilities each next application requires.

Reuse the existing Rust test infrastructure for the runner.
When implementation starts, place campaign applications under `tests/end_to_end/` with one directory per stage and ordinary source modules inside.
Keep requirements, C++ source, permitted companion specs, independent tests and mutation definitions together.
Record results only after actual runs. This plan creates no benchmark score.

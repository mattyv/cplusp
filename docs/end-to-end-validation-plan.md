# C+P end-to-end validation plan

Date: 2026-10-09. Status: planned. This document defines the programs and their execution order.
It does not record completed program runs.
Capability review: commit `7bbdc9201eebc9eb23b43900f1f1a7b8361a5aea`.

## What we are testing

Test the complete path from a program requirement to a working executable:

1. Review the requirement and formal contracts.
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

## Programs and order

Use one small executable driver for each program. The driver supplies inputs and checks outputs.
Keep file and console I/O outside the verified core and name that boundary.
The line ranges below are planning estimates for executable core code, excluding contracts and tests.
They are not acceptance targets.

| Order | Program | Approximate size | Required functional guarantee | New difficulty |
|---|---|---:|---|---|
| 1 | **Clamp and checked arithmetic** | 20–60 lines | Clamp returns the specified bound or original value. Checked addition reports overflow exactly and returns the sum otherwise. | Branches, integer bounds, success and failure results |
| 2 | **Sequence statistics** | 50–100 | Count matches the input length. Sum is exact for the declared domain. Minimum exists exactly when the input is nonempty and is an input element no larger than any other. | Loops, invariants, empty inputs, helper composition |
| 3 | **Decimal integer parser** | 60–140 | Accept exactly nonempty ASCII digit sequences whose numeric value fits `uint32_t`. Return that value. Reject invalid bytes and overflow. Permit leading zeros. | Byte spans, optional scalar, prefix invariants, rejection behavior |
| 4 | **Sorted lookup library** | 80–160 | Lower bound returns the first position with value at least the key. Membership is true exactly when the key occurs. Input satisfies the sorted precondition. | Quantifiers, duplicates, loop termination, caller proofs |
| 5 | **Binary command-frame decoder** | 120–240 | Validate a fixed version/kind/length header. Decode fields exactly. Consume one complete frame and report its length. Distinguish invalid input from incomplete input. | Slices, returned records, byte arithmetic, composition of parsers |
| 6 | **Recursive radix-tree lookup** | 100–220 | Lookup returns a value exactly when the well-formed tree stores the full key. Establish termination under the stated tree and depth conditions. | Recursive data, recursive specifications, nested sequences |
| 7 | **Bounded FIFO queue** | 120–260 | Push and pop preserve logical order through wraparound. Full or empty operations report failure and leave state unchanged. | Sequence writes, object initialization, state invariants, operation histories |
| 8 | **Account ledger** | 200–450 | Transfers preserve total funds, keep balances in range, and change only the named accounts. A rejected transfer changes nothing. Define self-transfer as a successful no-op. | Multiple state updates, conservation, failure atomicity, input validation |
| 9 | **Single-instrument limit order book** | 400–1,000 | Add, cancel and match obey price/time priority. Partial fills conserve quantity. Invalid commands leave state unchanged. | Interacting invariants, nested loops, ordered mutable collections, several modules |
| 10 | **Order-command replay application** | 600–1,500 total | Decode a command stream, queue commands and apply them in order. Final book and trade output match the specified sequential execution. | Complete application composition, module boundaries, evolving code, trusted I/O |

This order adds one main proof burden at a time.
Stages 1–4 establish the basic coding loop.
Stages 5–6 add structured input and recursive reasoning.
Stages 7–8 establish mutable state and atomic failure behavior.
Stages 9–10 combine the earlier results into a useful program.

### Scope choices before implementation

- Use fixed-width integer prices and quantities. Do not use floating point in the first order book.
- Keep all ten programs single-threaded. Concurrency needs a separate campaign and proof scope.
- Give mutable collections explicit capacities. Define capacity exhaustion as an observable result.
- For the order book, support limit orders, cancellation and partial fills first. Defer amend, market orders and multiple instruments.
- Use arrival sequence numbers for time priority. Define what happens when the sequence number cannot advance.
- Require unique live order IDs. State explicitly whether a completed or cancelled ID may be reused.
- Decide how a full book treats an incoming order that would match before leaving a remainder. Freeze this rule before coding.
- For replay, specify the first-error behavior, trailing incomplete frame behavior and exact command-consumption rule.
- Give the decoder a distinct incomplete result. Invalid bytes must not become a precondition that excludes external input.

## Use the current slice honestly

Existing examples often pair C++ with hand-written Dafny.
Reuse their requirements and fixtures, but qualify them through automatic translation.
Run one small feature probe before investing in each program's full implementation.

| Stages | Starting evidence at the reviewed commit | Check before committing to the stage |
|---|---|---|
| 1–4 | Translator fixtures cover branches, loops, read-only sequences, scalar optionals, calls and quantified contracts. | Prove the exact result types, arithmetic and companion definitions the program needs. These complete programs are not yet confirmed. |
| 5 | Subspan, scalar structs and contract slices have rules. | Check the tagged result record and every field. Optional-of-struct support is not established by the reviewed slice. Use an explicit status record if it preserves the reviewed API semantics. |
| 6 | The existing `radix_find` slice is reported as proved end to end. | Reproduce it from source, then add unseen keys, a changed helper and new wrong variants. Reuse the existing slice. |
| 7–9 | Member support is being added in steps. Read-only sequences do not establish sequence mutation support. | Require proved translation rules for each constructor, mutation and state effect used. Also check collection specifications and framing. |
| 10 | The public CLI proves one source file per invocation. | Prove every relevant body across the chosen files. Demonstrate caller coverage when a header or contract changes. Do not assume a repository-wide proof command exists. |

Relevant sources: [examples](../examples/README.md), decisions
[0074](decisions/0074-a-mutable-reference-to-a-struct-has-no-rule-yet.md),
[0076](decisions/0076-structs-that-hold-sequences-and-recursive-structs.md),
[0089](decisions/0089-member-functions-in-steps.md),
[0090](decisions/0090-a-pure-const-member-function-is-also-a-dafny-function.md),
the [CLI](../crates/cplusp/src/main.rs), and the [radix trial](trial-flashradixtree.md).
Recheck the latest decisions before each stage because the slice is changing.

A required construct that lacks a rule blocks that stage.
Record the smallest source that exposes the missing rule and implement that capability as a separate change.
Retain the original program requirement. Do not mark its central algorithm trusted just to obtain a pass.
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
Record the ordinary executable build and run cost separately from verification cost.

First establish that the full path works. Then test whether proof feedback improves coding results.
For that comparison, use paired tasks with the same model, requirements, reviewed contracts and total budget.
One arm uses tests. The other also receives C+P feedback.
Judge both with the same hidden executable tests and review.
Repeat with independent attempts. A few initial runs are a pilot, not a reliable effect estimate.

## First execution batch

1. Build the campaign around stage 1 and one intentional arithmetic error.
2. Confirm the entire source-to-diagnostic-to-repair-to-executable path.
3. Run stages 2 and 3 under the same harness.
4. Fix workflow defects before adding larger programs.
5. Continue in table order, adding only the capabilities each next program requires.

Reuse the existing Rust test infrastructure for the runner.
When implementation starts, place campaign programs under `tests/end_to_end/` with one directory per stage.
Keep requirements, C++ source, permitted companion specs, independent tests and mutation definitions together.
Record results only after actual runs. This plan creates no benchmark score.

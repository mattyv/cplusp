# Generate and challenge specifications

Use this workflow for C++ contracts and Dafny models, or for the Verus core.
Keep the repository's reviewer and coder roles. The coder implements reviewed contracts.
The reviewer decides changes to requirements, contracts and tests.

## Establish intent

1. Read the requirement, public interface, callers, tests and current implementation.
2. List the required outcomes, allowed inputs, state changes and failure behavior.
3. Map each outcome to a contract clause and an independent example or test.
4. Separate observed behavior from intended behavior. Mark an inference from code as a candidate until reviewed. Report conflicts instead of specifying a suspected bug as the requirement.
5. Snapshot the executable and reviewed contracts before adding annotations.

Specify results, preservation of data, allowed state changes and unchanged fields.
Check empty inputs, boundaries, duplicates and each outcome of a conditional result.
Use the supported companion-file definitions for C++ specification functions.
Read decision 0079 and its later amendments for declaration, naming and text restrictions.
Use the active Verus syntax and toolchain for core contracts. Do not copy Dafny syntax into Verus.

## Generate and prove in components

Read each component with its types, state and dependency contracts.
Check the subsystem contract top-down. Generate helper contracts and loop invariants bottom-up.
Treat recursive dependency groups together when individual functions cannot be specified independently.
Keep open helper obligations visible until all relevant bodies verify.

Run the project's actual verifier after meaningful annotation changes.
Use diagnostics to repair supporting invariants and proof steps.
Keep reviewed requirements and contracts fixed during proof repair.
Do not exclude valid inputs, weaken guarantees or introduce assumptions to make a proof pass.
Report a conflict to the reviewer if a contract needs correction.

Compare executable behavior with the snapshot after annotation work.
Report any executable change separately. Run the independent tests for that change.
For C++, check translation acceptance and fidelity separately from the Dafny proof.

## Challenge the contract

First verify the original body with the fixed contract and record the command and result.
If the baseline fails, resolve or report that failure before interpreting mutations.

Choose small, well-typed mutations that violate a listed requirement for an allowed input.
Write them in a scratch copy. Keep contracts, specification definitions and trusted assumptions fixed.
Re-run the same verification route on each variant.

| Requirement | Wrong body | Clause that should reject it |
|---|---|---|
| Sort preserves elements and duplicates | Return an empty sequence or remove repeated elements | Equal element multiplicities between input and output |
| Search reports membership | Always return false | The result is true if and only if the target occurs |
| An update changes only its named field | Update a second field too | Equality of all unchanged fields to their old values |
| A count includes the final element | Stop one element early | Result equals the specified count over the full input |

Give a concrete allowed input and the wrong result for each mutation.
Classify each run separately:

- **Verified:** the wrong variant passed. Report a possible missing clause, model mismatch or trusted assumption. Check the witness against the formal model.
- **Proof rejected:** record the failed obligation. A requirement-specific failure supports the contract. An unrelated arithmetic or invariant failure gives weaker evidence.
- **Translation refused or syntax failed:** the contract has not been tested by this variant.
- **Timeout or tool failure:** the result is inconclusive. Do not count it as detection.

Check that intended input classes satisfy the preconditions with caller proofs or concrete witnesses.
A witness shows one admissible input. It does not establish that every intended input is admitted.
Watch for contradictory preconditions and for postconditions that permit arbitrary results.
Passing these checks does not prove specification completeness.

## Report evidence

Record requirement coverage, baseline proof outcome, mutation witnesses and outcomes,
input-domain checks, executable changes, translation limits and remaining assumptions.
Include exact commands and tool versions for claims of execution.
If a tool is unavailable, label the assessment as static and list the unrun checks.
Use counts and concrete findings. Do not treat an LLM quality score as a certificate.

For a pilot, compare ordinary review with this workflow on the same held-out tasks,
requirements, model and total time or token budget. Include specification and proof-repair costs.
Judge executable correctness independently. Freeze the specification before evaluation mutations.
Keep evaluation mutations separate from those used to refine it.
Measure missed requirements and wrong variants that still verify, as well as verification success.

## Evidence behind the workflow

- [SpecSyn, Table 2](https://arxiv.org/html/2604.21570v1): with GPT-5, decomposition raised reference-specification coverage from 63.25% to 75.91%. Mutation refinement raised it from 70.57% to 75.91%. This is an author-reported C/ACSL preprint study of 50 source files. It supplies target properties.
- [AutoSpec+, Sections 5.1–5.4](https://aclanthology.org/2026.acl-demo.66.pdf): verifier feedback and iterative repair improved generation of proof-ready ACSL annotations. Overall pass@5 was 91.05%, versus 79.76% for AutoSpec. This measures verification success.
- [KVerus skills](https://github.com/asterinas/KVerus/tree/main/skills): separate specification work, proof repair, specification review and executable-semantic audit. The [ASE 2026 study](https://arxiv.org/html/2605.03822v1) evaluates an earlier proof-generation workflow and assumes correct specifications. It does not validate the current specification skill in isolation.

This is a C+P adaptation of those methods. Its effect on C+P has not yet been measured.
See [the research report](../../../docs/research/formal-verification-llm-coding-report.md) for broader evidence and limits.

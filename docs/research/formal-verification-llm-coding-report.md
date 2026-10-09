---
title: "Does formal verification improve LLM coding?"
subtitle: "Seven conclusions, with the evidence beside each claim"
date: "Evidence checked 9 October 2026"
lang: en
---

**Yes: reliable specifications and decomposed verification workflows have improved measured LLM results.** Experiments support generating contracts for smaller components and combining them into larger proofs. This supports C+P's architecture. Production defect reduction and lifetime cost savings still need measurement.

A **formal specification** is a precise, machine-checkable requirement. For a sorting function, it could require that the output is ordered and contains exactly the input elements, including duplicates. A plan guides implementation. The formal contract defines what must be proved.

## 1. Reliable specifications improve issue repair.

**SWE-Proof evaluated 500 real repository issues.** Supplied formal specifications raised issue resolution from **85.0% to 94.0–96.2%**: about **9–11 additional fixes per 100 issues**. Agents writing their own specifications stayed near baseline. [1]

| What the agent received | Passed the hidden tests |
|---|---:|
| Issue and repository. Ordinary coding baseline | 85.0% |
| Issue and repository. Agent writes its own formal specification | 83.8–85.6% |
| Issue, repository and supplied formal specification | 94.0–96.2% |

Only **46.0–61.4%** of independently generated specifications passed the authors' LLM-based audit. The main failure was omitting required behavior. [1, Table 3][1]

**Limit:** this September 2026 preprint supplies extra requirements and localization information, so it does not isolate the prover's contribution. Test resolution also differs from verified success: the latter was **93.6–95.0%** with supplied specifications. [1, Table 2][1]

**Implication:** review the contract as carefully as the implementation. A proof of an incomplete contract leaves missing requirements unchecked.

**Narrow tasks show substantial progress.** In *Agentic Proving*, authors judged generated specifications defensible for **159/161 functions (98.8%)**. This consolidated three prompting rounds and manual review on HumanEval-style tasks. It demonstrates progress on function contracts, rather than automatic capture of repository-wide requirements. [5]

## 2. Decomposition helps agents generate useful specifications.

**There is direct experimental support for dividing verification into smaller tasks.** These comparisons are more informative than high success rates on isolated functions:

| Study | Comparison | Result |
|---|---|---|
| **AutoSpec**, CAV 2024 | Whole-program prompting → decomposition and hierarchical specification generation, using the same model | **9/51 → 26/51** programs' target properties verified. Full workflow with refinement: **31/51**. [2, Section 4.5][2] |
| **SpecSyn**, April 2026 preprint | Decomposition disabled → enabled, with GPT-5 in both variants | Verifiable specification clauses: **85.29% → 96.68%**. Coverage of reference specifications: **63.25% → 75.91%**. [7, Table 2][7] |
| **ConVer**, May 2026 preprint | Direct verification → LLM-generated contracts and decomposition, on 24 translated C models | **10/24 → 15/24** verified with the GPT-OSS backend. These are bounded verification results. [8, Section VI-C][8] |

SpecSyn used **50 programs from 14 sources**. Its percentages are averages across source groups, measuring clause verifiability and reference coverage rather than complete-program correctness. [7, Sections 4.3–4.4][7]

**Limit:** these workflows start with code and target properties. They test decomposition together with structured synthesis or abstraction. They do not isolate function length or demonstrate complete requirements generation from a vague request.

**Implication:** small components with useful contracts have empirical support as a verification strategy. Keeping each function short is only one part of that strategy.

## 3. Component proofs can compound into program proofs.

**Yes: checked contracts let callers reuse guarantees.** A caller proves that it meets the callee's input requirements, then uses the callee's promised result. This is standard modular verification. [4]

For example:

| Component | Contract needed |
|---|---|
| Sort | Output is ordered **and preserves every input element**. |
| Binary search | On ordered input, reports whether the target exists. |
| Sort, then search | Reports whether the target existed in the **original input**. |

The preservation clause makes the composition work. Returning an empty array satisfies “output is ordered” but loses the data.

If a replacement sort still satisfies the same contract, callers can retain their reasoning. A complete subsystem proof must also cover shared state and dependency assumptions. Concurrent programs additionally require reasoning about interference between components. Iris supports this. Whole-program claims require coverage of all relevant behavior. Unverified dependencies remain explicit assumptions. [4, sections on methods and framing][4], [6]

**Implication:** reusable contracts are a plausible source of compounding value. The size of the long-term maintenance saving remains an empirical question.

**Proof-aware design also helps larger synthesis.** IDS generated verified distributed-store implementations for **7/7 specification targets**. When joint code/proof discovery was disabled, only **1/7** reached the same success threshold: at least two successful runs out of three. This supports adapting the implementation to make proofs tractable. The May 2026 preprint uses supplied specifications and a small seven-target sample. [3, Table 2 and Section 5.4][3]

## 4. A proof must describe the executable you ship.

**A verified model supports a C++ claim only when it faithfully represents that C++.** Arithmetic, mutation and evaluation order must retain their meaning through translation.

SWE-Proof checks callee assumptions and model-to-patch correspondence through execution and audit. Its authors explicitly leave “verification implies issue resolution” unproved. [1, Section 5][1]

**Implication for C+P:** prove or validate translation correctness, reject unsupported constructs, and expose assumptions. A successful Dafny check alone cannot establish that the C++ translation preserved behavior.

## 5. C+P's practical payoff needs its own measurement.

**The reviewed studies do not establish C+P's defect reduction or total cost saving.** Their benchmarks support a pilot. Their percentages cannot predict this tool's results.

Run a comparison on representative changes:

- **Hold information and budget constant.** Give both groups the same agent, tasks, reviewed contracts and generation budget. Compare tests alone with tests plus proof feedback.
- **Judge the executable independently.** Use hidden tests, adversarial cases and human review. Count incorrect changes that still pass verification.
- **Count the full cost.** Include contract authoring, model calls, proof repair and maintenance. Report independently correct changes per hour and per dollar.

For C+P, start with a subsystem requirement, derive component contracts, implement small functions, and verify their composition. Compare that workflow with whole-subsystem generation under the same budget. Expand when the measured correctness gain justifies the added work.

## 6. SPARK supplies a whole-program development method.

**The engineering method transfers to Dafny.** SPARK supports contracts before implementations exist.
Dafny also supports modular proof, abstract interfaces and module refinement. [9][9], [12][12]

| Practice | Application to C+P |
|---|---|
| Define requirements through package specifications. | Derive subsystem requirements, component contracts and function contracts before implementation. |
| Describe state and dependencies. | Pass State values explicitly. Define permitted changes and preserve the other fields. |
| Prove integration. | Prove callee preconditions at each call. Prove that component guarantees establish the subsystem requirement. |
| Establish initialization guarantees. | Prove the initial state meets the conditions required by entry points. |
| Maintain proof results. | Run verification during development and across the program. Record all remaining assumptions. |

SPARK documents package state abstraction, initialization contracts, team workflows and assumption management. [10][10], [11][11]
These sources provide engineering guidance. They add no measured estimate of improvement in LLM coding.

**Function length alone is insufficient.** Choose boundaries that let callers use stable contracts.
Review those contracts against the subsystem requirement.
A successful proof can establish selected properties without establishing complete functional correctness. [9][9]

**C+P adds a translation obligation.** SPARK analyses the Ada/SPARK source.
C+P proves a Dafny model of C++.
Validate that each accepted construct preserves the relevant C++ behavior.
Include arithmetic, state changes, aliasing, lifetime and evaluation order.
Use the rules of the current translator slice.
A hand-written model of a future feature does not make that feature available to the translator.

For agent changes, use this sequence:

1. Define the subsystem requirement.
2. Derive and review component contracts, types and state effects.
3. Implement and prove each component.
4. Prove that the components establish the subsystem requirement.
5. Check C++ execution independently and validate translation behavior.
6. Report proof scope, unproved checks and trusted assumptions.

Do not weaken a contract or add an assumption merely to obtain a successful proof.
Report a requirements conflict for review.
Dafny requires all relevant implementations to verify for a complete program claim. [12][12]

## 7. Reusable skills exist. Their specification impact needs careful attribution.

**Use evaluated methods, then measure the local skill.** KVerus provides installable Verus skills.
SpecSyn and AutoSpec+ provide evaluated specification workflows.
Their results measure different outcomes.

| Candidate | Evidence | What it establishes |
|---|---|---|
| **KVerus**: specification, repair, review and behavior-audit skills | Earlier ASE 2026 workflow verified **251/313 tasks (80.2%)**, versus **178/313 (56.9%)** for AutoVerus. [13][13] | Better proof generation under the study conditions. The paper assumes correct specifications. It does **not** establish the current specification skill's quality. The evaluated workflow is on the repository's `ase-26` branch. [14][14] |
| **SpecSyn**: decomposition and mutation refinement | With GPT-5, adding mutation refinement raised average reference-specification coverage **70.57% → 75.91%**. Adding decomposition raised it **63.25% → 75.91%**. [7, Table 2][7] | Direct evidence of stronger generated supporting specifications on 50 C source files. Verification targets are supplied. This is a preprint and does not establish recovery of all intended requirements. |
| **AutoSpec+**: generate, verify and repair ACSL annotations | ACL 2026 evaluation reports **91.05% pass@5**, versus **79.76% for AutoSpec**, on the comparison suites. [15, Table 3][15] | Improved verification success within five attempts. The system includes model ensembles. This is not an isolated measure of specification completeness. |

**Implication for C+P:** adapt KVerus's separate workflow stages and SpecSyn's mutation checks.
Use the existing project skill and reviewer roles.
This adaptation has not yet been evaluated on C+P.

The reviewer should freeze the contract, verify the baseline, and try small wrong implementations.
For sorting, return an empty sequence or drop duplicates.
For search, always return false.
For an update, change an unrelated field.
Give an allowed input that exposes the wrong result for each mutation.
Record whether the proof rejects it, the wrong body verifies, or the check is inconclusive.
A translation refusal, syntax failure or timeout does not show that the contract catches the bug.

Also check that preconditions admit intended inputs.
Compare executable behavior before and after annotations.
Keep requirements review independent of implementation inspection.
Code-derived contracts can accurately describe an existing bug.
Neither successful verification nor rejection of a finite mutation set proves specification completeness.

See [the skill's specification-review workflow](../../skills/cplusp-dafny/references/specification-review.md).
For the pilot in section 5, add missed requirements and wrong variants that still verify to the measurements.
Keep evaluation mutations separate from the ones used to refine the specification.

## Sources

1. **SWE-Proof** (September 2026 preprint, v2). [Tables 2–3 and Section 5](https://arxiv.org/html/2609.21190v2).
2. **AutoSpec** (CAV 2024). [Section 4.5 and Table 5: decomposition experiment](https://link.springer.com/chapter/10.1007/978-3-031-65630-9_16).
3. **Inductive Deductive Synthesis** (May 2026 preprint). [Section 5.4 and Table 2: joint-design ablation](https://arxiv.org/pdf/2605.23109v1).
4. **Dafny documentation**. [Caller/callee contracts](https://dafny.org/latest/OnlineTutorial/guide) and [reference manual: methods and framing](https://dafny.org/latest/DafnyRef/DafnyRef.html).
5. **Agentic Proving for Program Verification** (May 2026 preprint). [Section 3.1: specification generation and manual classification](https://arxiv.org/html/2605.23772v1).
6. **Iris**. [Framework for reasoning about concurrent programs](https://iris-project.org/).
7. **SpecSyn** (April 2026 preprint). [Sections 4.3–4.4 and Table 2: decomposition and specification quality](https://arxiv.org/html/2604.21570v1).
8. **ConVer** (May 2026 preprint). [Section VI-C: contract-based decomposition of C models](https://arxiv.org/html/2605.27051v1).

9. **SPARK documentation**. [Constructive modular development](https://docs.adacore.com/live/wave/spark2014/html/spark2014_rm/introduction.html), [contract defaults and functional correctness](https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_write_subprogram_contracts.html).
10. **SPARK package contracts**. [State abstraction and initialization](https://docs.adacore.com/spark2014-docs/html/ug/en/source/package_contracts.html).
11. **SPARK team workflows**. [Continuous analysis and assumption management](https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_use_gnatprove_in_a_team.html).
12. **Dafny documentation**. [Modules and refinement](https://dafny.org/dafny/OnlineTutorial/Modules), [complete verification and assumptions](https://dafny.org/latest/DafnyRef/DafnyRef.html).
13. **KVerus** (ASE 2026, Industry Track). [Table 1 and Section 6.1: proof-generation results and assumed specification correctness](https://arxiv.org/html/2605.03822v1).
14. **KVerus repository**. [Installable skills and the evaluated `ase-26` workflow](https://github.com/asterinas/KVerus), [specification skill](https://github.com/asterinas/KVerus/blob/main/skills/kverus-spec/SKILL.md).
15. **AutoSpec+** (ACL 2026 System Demonstrations). [Tables 2–3 and Section 5: specification-generation evaluation](https://aclanthology.org/2026.acl-demo.66.pdf), [runnable tool](https://github.com/Xidian-ICTT-GZ/AutoSpec).

*This brief retains the earlier review's strongest evidence. Results come from distinct benchmarks. This report gives no pooled effect estimate.*

[1]: https://arxiv.org/html/2609.21190v2
[2]: https://link.springer.com/chapter/10.1007/978-3-031-65630-9_16
[3]: https://arxiv.org/pdf/2605.23109v1
[4]: https://dafny.org/latest/DafnyRef/DafnyRef.html
[5]: https://arxiv.org/html/2605.23772v1
[6]: https://iris-project.org/
[7]: https://arxiv.org/html/2604.21570v1
[8]: https://arxiv.org/html/2605.27051v1
[9]: https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_write_subprogram_contracts.html
[10]: https://docs.adacore.com/spark2014-docs/html/ug/en/source/package_contracts.html
[11]: https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_use_gnatprove_in_a_team.html
[12]: https://dafny.org/latest/DafnyRef/DafnyRef.html
[13]: https://arxiv.org/html/2605.03822v1
[14]: https://github.com/asterinas/KVerus
[15]: https://aclanthology.org/2026.acl-demo.66.pdf

# 0231: Separate guides for users and contributors

The README introduces the tool and links to two starting paths.
`docs/getting-started.md` covers setup, a passing proof, a failing proof,
commands and result interpretation. `docs/contributing.md` covers the code
boundaries, regression tests, Verus verification and review.

The design plan remains a record of architecture and proposals. It must name
unimplemented features as proposals. The current CLI has no automatic caller
tracking, incremental proof cache or selectable second prover.

The documentation distinguishes a gate pass, a successful translation and a
successful proof. It also distinguishes handwritten models from automatic
translation. Verus proves core implementations against their specifications.
That does not establish full equivalence between C++ and the generated model.

The policy example includes the required `construct` field. The soundness
document now states the contract arithmetic of decisions 0057 and 0088:
integer expressions in contracts use exact integers. C++ body operations
retain the model's type and range obligations.

This change updates documentation only. It changes no checker behavior.

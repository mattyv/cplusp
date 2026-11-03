# Trial: ilp_for

The 2026-11-03 trial used ilp_for to test cplusp's ability to handle existing C++.
The main finding is a coverage gap: cplusp cannot yet prove the actual generic loop library.
These C++ features need faithful models and acceptance tests. Refusing them safely does not remove the product gap.

## What ran

The trial used cplusp revision `af9b5cb46f6260208d48859bea033102ddecdf9a`
and ilp_for revision `7f012bf8c285d7d44bbb8e8996ccb7c3e0061e09`.
The toolchain used Dafny 4.11.0, Clang 18.1.8 and GCC 14.2 on x86-64 Debian.

| Check | Result | Scope |
| --- | --- | --- |
| Documented clamp example | Proved | Existing cplusp baseline |
| Extracted block-bound function for uint32_t and N=4 | Proved through cplusp | Manual specialization, not the original template |
| Wrong extracted function returning start | Contract rejected | Fixed-contract mutation |
| Actual library through cplusp prove | Gate refused | No automatic proof of the library |
| Handwritten modular bounds and traversal models | Dafny proved | Abstract arithmetic and action traces only |

The handwritten proofs do not establish automatic C++ translation, callback state, argument types, value categories, object lifetimes or return storage safety.
The traversal model uses mathematical integers and a fixed sequence of callback actions.
It does not establish machine overflow safety or arbitrary callback equivalence.

## Gaps exposed

The gate rejected non-type template parameters, including the loop's block size and mode.
It also reported specializations, dependent template names, function-like macros, built-in integer types, pointer restrictions and unlisted constructs or attributes.
These diagnostics report policy refusals. The direct run stopped before translation, so its diagnostics are not a complete translator capability test.

Non-type template instantiations need general-purpose support. Instantiation determines a concrete block size, but cplusp currently rejects that template form.
Generic callbacks also need faithful treatment of the instantiated call, captures, references, side effects and control state.
Loosening policy alone cannot establish that translation preserves those behaviors.

The trial found two actual differences between simple and unrolled loops:

- For int8_t bounds 0..5 and block size 4, a generic by-value callback sees int8_t five times in simple mode.
  In unrolled mode, it sees int8_t once. The four block arguments promote to int.
- For int bounds 0..5, a forwarding-reference callback sees an lvalue five times in simple mode and once in unrolled mode.
  Tail arguments refer to the internal index. Block arguments are temporary values.

GCC and Clang reproduced both differences. Specification review and executable checks found them, not a cplusp proof failure.
A model that preserves only numeric index values misses both differences.
The original library's mode-equivalence tests provide independent evidence for the intended behavior.
The subsequent ilp_for fix, commit `5c19dea5829ee67925c63871ec5972142c5ce9df`, fixes both differences. The trial above describes the pinned original revision.

Range iterators, typed return values and untyped return storage require further isolated acceptance tests.
The successful handwritten proofs establish no support for their lifetime or byte-representation rules.

## Next acceptance tests

1. Instantiate a small function with an integer template parameter. Prove its contract through the normal gate, translator and prover.
   Reject a wrong body with the same contract. Test multiple instantiations and keep their identities distinct.
2. Call a generic callback with narrow integer arguments. Preserve promotions and prove the selected overload's contract.
3. Distinguish lvalue and temporary callback arguments. Check reference effects, captures and observable state changes.
4. Compose callback contracts with loop termination and early exits. Then isolate range and return-storage obligations.

These steps propose tool improvements. This trial adds no translator support and makes no claim that ilp_for is fully proved.

## Diagnostic improvement

The original refusal printed 393 findings in 195,130 bytes.
The local rendering fix prints 35 distinct reasons in 81 lines and 16,554 bytes.
Both runs exit 1. Complete JSON output remains identical for all 393 findings.
This removes repeated explanations while preserving the evidence. It does not close the language coverage gaps.

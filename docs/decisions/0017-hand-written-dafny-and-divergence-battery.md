# 0017: No translator yet. People and the LLM write the Dafny, under rules found by a divergence battery

Date: 2026-10-03. Status: decided.

## Decision

For the first cut nobody builds a translator. A person or the LLM writes the Dafny model of a C+P function by hand, as a line-for-line transliteration under written rules. The rules come from a battery of cases. Each case has five parts. The C++. A naive Dafny model, written to show where it diverges from the C++. A mitigated model. A witness that drives the C++ to the edge. The rule in words. The rules live in `skills/cplusp-dafny/SKILL.md`, which the LLM reads. A test runs every case.

## Why

The translator would be the largest trusted component in the design. Building it before we have written a dozen models by hand means automating rules we have not learned. The battery finds the rules one divergence at a time. The first case already changed one. `int32_t` must become a bounded type, because the unbounded model proved a function with an overflow bug.

## What changes

`divergence/`, `skills/cplusp-dafny/`, the `divergence` test crate. The soundness document fills gap 3 and gap 4 from the cases. Mitigations on the C++ side become policy rows. The rules become the translator's specification when a translator is built.

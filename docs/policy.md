# Gate configuration: `cplusp-policy.yaml`

Oct 3, 2026. Draft. This file is the rule list from the plan, in the form the gate reads.

## One file, one entry per row

The subset table in the plan and `cplusp-policy.yaml` are the same list. Every row is one entry. An entry says four things: what the construct is, what we decided, why, and how the gate detects it. The gate never has a rule that is not in this file.

```yaml
# cplusp-policy.yaml
version: 1

defaults:
  new_functions: verified        # verified | plain
  edited_functions: keep         # an edited function keeps its kind
  exceptions:
    reason_required: true        # trusted, plain and assume markers need a reason
    approval: report             # report | require-human   (open question in the plan)

rules:
  - id: goto
    area: control
    decision: ban
    why: No benefit.
    use_instead: A loop.
    detect:
      - check: cppcoreguidelines-avoid-goto

  - id: c_style_casts
    area: casts
    decision: ban
    why: Hides what kind of cast it is. All forms, including plain numeric narrowing.
    use_instead: static_cast, or std::bit_cast for a byte view.
    detect:
      - check: google-readability-casting

  - id: reinterpret_cast
    area: casts
    decision: trusted_only
    why: Defeats the type model. Most forms are UB.
    use_instead: std::bit_cast, or mark the function trusted with a reason.
    detect:
      - check: cppcoreguidelines-pro-type-reinterpret-cast

  - id: unions
    area: types
    decision: ban
    why: Type punning breaks the memory model.
    use_instead: std::variant.
    detect:
      - check: cppcoreguidelines-pro-type-union-access   # fires on use
      - check: cplusp-union-decl                         # fires on the declaration

  - id: iterators
    area: library
    decision: restrict
    limit: Range-for only. No iterator arithmetic, no stored iterators.
    why: Iterator arithmetic is pointer arithmetic in disguise.
    use_instead: A range-for loop, or an index the prover can check.
    detect:
      - check: cplusp-iterator-arithmetic

  - id: multiple_inheritance
    area: classes
    decision: restrict
    limit: Extra bases must be pure interfaces.
    why: Keep the object model simple.
    use_instead: One concrete base plus interfaces.
    detect:
      - check: cplusp-multiple-inheritance
        options:
          AllowPureInterfaces: true

  - id: global_state
    area: state
    decision: restrict
    limit: Listed in the contract's reads or modifies clause. Constants exempt.
    why: Hidden state breaks modular proofs.
    use_instead: A reads or modifies clause naming the variable, or a parameter.
    detect:
      - check: cplusp-unlisted-state

  - id: variable_index
    area: library
    decision: allow
    stage: prover
    why: The prover proves the index is in range.
    detect:                                              # dormant while the decision is allow
      - check: cppcoreguidelines-pro-bounds-constant-array-index
```

## The fields

| Field | Required | Meaning |
| --- | --- | --- |
| `id` | Yes | Stable name for the construct, in snake_case. Overrides and reports use it. Also the folder name of the rule's sample pair |
| `construct` | Yes | The construct as the table and the messages name it, for example `C-style casts` |
| `canonical` | No | What MISRA, the Core Guidelines or eCv++ say. Documentation only. `cplusp policy doc` prints it |
| `area` | Yes | The grouping from the table: types, arithmetic, memory, library, casts, classes, templates, control, concurrency, state, platform |
| `decision` | Yes | One of `allow`, `restrict`, `trusted_only`, `ban` |
| `limit` | For `restrict` | The limit in one sentence. The gate puts it in the message |
| `why` | Yes | The reason from the table. The gate puts it in the message |
| `use_instead` | For everything but `allow` | What the bot should write instead. The gate puts it in the message |
| `stage` | No | `gate`, `prover`, `spec` or `none`. Default `gate` when `detect` is present, else `none`. The gate enforces only `gate` entries. A `prover`, `spec` or `none` entry needs no `detect` and no `use_instead`, and the gate treats it as `allow`, whatever its decision says. The decision still matters for overrides: a team may not loosen it without a reason |
| `detect` | For everything but `allow` | The checks that find the construct. Each has a `check` name and optional `options` |

A `detect` list on an `allow` entry is dormant. It exists so that flipping the decision to `ban` is a one-word edit. If a construct has no check that fits, write a new `cplusp-*` check and name it here. That is the "add a rule" recipe from the plan.

## What the gate does with an entry

For each entry with a decision other than `allow`, the gate:

1. Turns on every check in `detect`, with its options, in a generated clang-tidy config.
2. Maps each finding from those checks back to the entry by check name.
3. Decides whether the finding stands. A `trusted_only` finding inside a trusted function is dropped. Everything else stands.
4. Writes the message from the entry's fields.

The generated config is a build artifact. Nobody edits it.

```yaml
# .cplusp/clang-tidy.generated.yaml
Checks: >-
  -*,
  cppcoreguidelines-avoid-goto,
  google-readability-casting,
  cppcoreguidelines-pro-type-reinterpret-cast,
  cppcoreguidelines-pro-type-union-access,
  cplusp-union-decl,
  cplusp-iterator-arithmetic,
  cplusp-multiple-inheritance,
  cplusp-markers,
  cplusp-index
WarningsAsErrors: '*'
CheckOptions:
  cplusp-multiple-inheritance.AllowPureInterfaces: true
```

The message has one shape per decision. The gate fills the braces from the entry. The construct name is followed by a colon, so the sentence reads the same for singular and plural constructs.

```
ban:           Not provable: {file}:{line}: {construct}: not allowed in verified code. {why} Use {use_instead}
trusted_only:  Not provable: {file}:{line}: {construct}: allowed only in trusted code. {why} Use {use_instead}
restrict:      Not provable: {file}:{line}: {construct}: outside its limit. Limit: {limit} Use {use_instead}
```

For example, the `iterators` entry above produces:

```
Not provable: src/scan.cpp:12: Iterators: outside its limit. Limit: Range-for only. Use a range-for loop, or an index the prover can check.
```

The function name joins the location once the clang-tidy plugin's `cplusp-index` check exists. Until then the gate treats every finding as inside a verified function.

## Checking the policy

`cplusp policy check` prints `ok: 52 rules, 36 enforced by the gate` or one line per problem on stderr, in the form `{id}: {problem}`. `cplusp policy emit` prints the generated clang-tidy config. Both take `--policy FILE` for a team policy.

## Reading the policy as a table

`cplusp policy show` prints the policy as the subset table from the plan: area, construct, decision, limit, stage. One screen, sorted by area. Team overrides show in their own column.

The table in the plan is generated from the default policy by `cplusp policy doc`. Nobody edits it by hand. The file and the table cannot drift, because one is made from the other. Decided Oct 3, 2026.

## A team's own policy

A repo may carry its own `cplusp-policy.yaml`. It extends the list that ships with the tool and overrides decisions by `id`. It does not repeat the fields it does not change.

```yaml
# a team repo's cplusp-policy.yaml
version: 1
extends: cplusp:default

rules:
  - id: recursion
    decision: ban                # tighter than the default restrict

  - id: floating_point
    decision: allow              # looser than the default
    loosened_because: Numerics team. Float values are checked by tests here, not proofs.
```

Tightening is always allowed. Loosening needs `loosened_because`, and every run prints the loosened entries at the top of its report. Whether loosening should also need a human approval is open, like the marker approval in the plan.

## What the tool rejects

The gate refuses to run on a policy that breaks any of these:

- A `decision` outside the four values.
- A `restrict` entry without a `limit`.
- A `ban`, `trusted_only` or `restrict` entry without `detect` or without `use_instead`.
- Two entries with the same `id`.
- An override whose `id` is not in the list it extends.
- An override that loosens a decision without `loosened_because`.
- A `check` name that the pinned clang-tidy plus our plugin does not know.

## Where the sample pairs live

Every entry has a folder named after its `id` in the cplusp repo:

```
rules/
  goto/
    allowed.cpp        # compiles, passes the gate
    banned.cpp         # compiles, fails the gate on marked lines
  c_style_casts/
    allowed.cpp
    banned.cpp
```

The test suite runs every pair against the default policy. A pair that disagrees with its entry fails the build. That is how we found that the check the plan first named for C-style casts let `(int)big` through.

## Decided

- **One file.** Each entry holds both the decision and the detection. The table and the file stay one list. Decided Oct 3, 2026.
- **Loosening.** A team policy may weaken a rule. It must give `loosened_because`, and every run prints the loosened entries at the top of its report. Decided Oct 3, 2026.

## Open choices

- **Granularity of a team policy.** One per repo, as drafted, or one per directory as clang-tidy itself allows.

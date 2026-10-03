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
      - check: cppcoreguidelines-pro-type-union-access     # fires on use
      - matcher: recordDecl(isUnion(), isDefinition())     # fires on the declaration

  - id: iterators
    area: library
    decision: restrict
    limit: Range-for only. No iterator arithmetic, no stored iterators.
    why: Iterator arithmetic is pointer arithmetic in disguise.
    use_instead: A range-for loop, or an index the prover can check.
    detect:
      - check: cplusp-iterator-arithmetic

  - id: uninitialised_variables
    area: types
    decision: ban
    why: Reading them is UB.
    use_instead: an initialiser on every declaration.
    detect:
      - check: cppcoreguidelines-init-variables
      - check: cppcoreguidelines-pro-type-member-init
        options:
          IgnoreArrays: "true"

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
| `stage` | No | `gate`, `prover`, `spec` or `none`. Default `none` for an `allow` entry with no `detect`, else `gate`, so a ban without `detect` fails closed. The gate enforces an entry when its stage is `gate`, or when it has a `detect` list and a decision other than `allow`. That second case is how a dormant `detect` on a prover row wakes up when a team flips the row to `ban`. A `prover`, `spec` or `none` entry without `detect` needs no `use_instead`, and the gate treats it as `allow`. Its decision still matters for overrides: a team may not loosen it without a reason |
| `detect` | For everything but `allow` | The checks that find the construct. Each entry is either `check: NAME` with optional `options`, or `matcher: PATTERN`, a clang AST matcher written as `clang-query` writes it |

A `matcher` entry needs no C++. The gate hands the pattern to one generic check in the plugin, `cplusp-matcher`, as an option named after the rule: `cplusp-matcher.{id}/{n}: '{pattern}'`. Here `n` counts the rule's patterns from 1. The check compiles the pattern when clang-tidy starts and reports every match with the rule id as its message. A pattern that does not parse is a configuration error, and the gate exits 2 naming the rule. A pattern runs on the full tree, so it sees implicit nodes, such as the cast that `sign_compare` matches. Twenty-six rules use patterns today. The rules that need real code keep a hand-written check.

A `detect` list on an `allow` entry is dormant. It exists so that flipping the decision to `ban` is a one-word edit. Give such an entry a `use_instead` too, so the message is complete on the day it wakes up. If a construct has no check that fits, write a new `cplusp-*` check and name it here. That is the "add a rule" recipe from the plan.

## What the gate does with an entry

For each entry with a decision other than `allow`, the gate:

1. Turns on every check in `detect`, with its options, in a generated clang-tidy config.
2. Maps each finding from those checks back to the entry by check name.
3. Decides whether the finding stands. A `trusted_only` finding inside a trusted function is dropped. Everything else stands.
4. Writes the message from the entry's fields.

The generated config is a build artifact. Nobody edits it. The gate writes it to a temporary file for each run, and `cplusp policy emit` prints it.

```yaml
# Generated by cplusp from cplusp-policy.yaml. Do not edit.
Checks: '-*,cppcoreguidelines-avoid-goto,google-readability-casting,cppcoreguidelines-pro-type-reinterpret-cast,cppcoreguidelines-pro-type-union-access,cplusp-matcher,cplusp-iterator-arithmetic,cppcoreguidelines-init-variables,cppcoreguidelines-pro-type-member-init'
WarningsAsErrors: '*'
HeaderFilterRegex: '.*'
ExtraArgs: ['-Wreorder-ctor']
CheckOptions:
  cplusp-matcher.unions/1: 'recordDecl(isUnion(), isDefinition())'
  cppcoreguidelines-pro-type-member-init.IgnoreArrays: 'true'
```

`ExtraArgs` turns on the compiler warning behind every `clang-diagnostic-` check the policy names, because clang leaves some of them off. `HeaderFilterRegex` makes the gate judge project headers that the given files include. System headers stay out. To pass a header on its own, add `-x c++` after `--`.

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

The function name joins the location once the clang-tidy plugin's `cplusp-index` check exists. Until then the gate treats every finding as inside a verified function. Paths print relative to the working directory when they are under it.

Two findings come from the gate itself, not from a policy row:

- A `NOLINT` comment in a given file. It would silence clang-tidy. The gate reports it as a finding, with this message: `NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.`
- A file the gate cannot read: `cannot read {file}`, exit 2.

`cplusp gate --json` prints one JSON object per finding per line and nothing else. The bot's skill and the tests read this form:

```
{"rule":"c_style_casts","check":"google-readability-casting","file":"rules/c_style_casts/banned.cpp","line":4,"decision":"ban","message":"..."}
```

## Checking the policy

`cplusp policy check` prints `ok: 63 rules, 49 enforced by the gate` or one line per problem on stderr, in the form `{id}: {problem}`. `cplusp policy emit` prints the generated clang-tidy config. Both take `--policy FILE` for a team policy. A file without `rules` is a parse error. So is a rule or override with a field it may not carry. A misspelt key therefore cannot drop a team's overrides on the floor.

## Reading the policy as a table

`cplusp policy show` prints one row per rule in file order: area, id, decision, stage, limit, note. The note column says `loosened` for a rule a team policy loosened. Every command also prints loosened rules on stderr, one line each: `loosened: {id}. {reason}`.

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
- A `check` name that the pinned clang-tidy plus our plugin does not know. Names that start with `clang-diagnostic-` are compiler warnings and always count as known.

The gate also refuses to judge a file that does not compile. It prints `does not compile: {file}:{line}: {message}` for each compiler error and exits 2. Code the compiler rejects is not provable, and a quiet "no findings" would say otherwise. Any `clang-diagnostic-` finding that no rule claims counts as a compiler error, because the generated config turns every other warning off.

`cplusp gate --plugin PATH` loads the clang-tidy plugin from `clang-tidy/`. A plugin that fails to load is a refusal, exit 2, because clang-tidy itself would carry on without it. The plugin is built with `cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin`. Without it the generic check and the hand-written checks are names without a check behind them, and the warning below says so.

Three more refusals, all exit 2:

- `-p DIR` without a `DIR/compile_commands.json`. clang-tidy would quietly run with no flags.
- `-p` together with trailing `--` flags. clang-tidy would quietly drop `-p`. The message is `Use -p or --, not both.`
- No clang-tidy on the machine when running `policy check`. Without it the check names cannot be checked.

Trailing `--` flags are trusted. `-w` or `-Wno-everything` there hides the compiler-warning rows such as `return_ref_to_local`.

Checks the plugin does not provide yet are names without a check behind them. Every `gate` run says so on stderr: `warning: not enforced, no such check: cplusp-recursion, cplusp-unlisted-state`. An "ok" from the gate is only as strong as that line is short. Without `--plugin`, the generic check is on that list too.

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

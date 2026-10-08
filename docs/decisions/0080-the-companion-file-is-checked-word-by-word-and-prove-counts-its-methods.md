# 0080: The companion file is checked word by word, and prove counts the methods that Dafny verified

Date: 2026-10-08. Status: decided. Amends 0079 on the check of the companion file and on the verdict of 0077.

## Decision

- The shell reads the companion file as Dafny reads it. A comment can hold another comment, as in Dafny. The shell refuses a comment that does not end, and each `"`, `@` and `{:` anywhere in the file. A specification over the model needs no string, no attribute and no `@` label.
- Each word of the file that is a keyword of Dafny must be on a short list. These are the words of the list. For declarations and contracts: `function`, `predicate`, `ghost`, `requires`, `ensures`, `decreases` and `reads`. For expressions: `if`, `then`, `else`, `var`, `match`, `case`, `forall`, `exists`, `true`, `false`, `as`, `is` and `in`. For types: `int`, `nat`, `bool`, `seq`, `set`, `map` and `multiset`. The shell refuses every other keyword wherever it stands, such as `type`, `newtype`, `witness`, `lemma`, `assume` and `by`. A keyword is never a name, so the list refuses no honest file. It replaces the check of the first word of each declaration in 0079.
- `ghost` may stand before `function` and `predicate`. A ghost function adds no axiom, and it may hold a quantifier that a compiled function may not.
- The verdict of 0077 takes a sixth fact: the number of methods in the model, which the shell prints. `Proved` needs Dafny to report at least that number of verified items. So a model that Dafny did not see in full never proves.
- Dafny gives no summary when it cannot resolve the file, and gives a line `N resolution/type errors detected` instead. That line counts as a summary with N errors and no time-out. Each error prints at its C++ or companion place as `Dafny says:` and the message. The run is not proved, with exit 1, and it is no failure of the tool.
- 0079 says that the scan and the warning check each other. That is not so. Dafny warns only for an `ensures` line on a function with no body. A function with no body and no `ensures` gets no warning, and an empty type can make it a proof of false. The list of keywords refuses each way to declare such a type. The warning check of 0079 stays for a function with no body and an `ensures` line. The check of the methods that Dafny verified catches a model that a comment hides.

## Why

The review of the green step of 0079 found four files of the companion that made a wrong body prove. An unclosed comment hid the whole model. A string held `/*` and hid an axiom from the scan. A nested comment made the scan think it was in a body. And a `newtype` after a `)` was no declaration for the scan. Each case came from a scan that read other text than Dafny reads. A list of the words that may appear asks less of the scan: it must find the words, not the shape of the file.

## What stays trusted

The scan stays a trusted edge in the shell, listed in `docs/plan.md`, until the lexer moves into the core, decision 0077. The list of keywords comes from the grammar of Dafny 4.11.

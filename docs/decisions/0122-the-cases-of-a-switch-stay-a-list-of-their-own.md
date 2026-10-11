# 0122: The cases of a switch stay a list of their own

Date: 2026-10-11. Status: decided. Amends 0121.

## Decision

Step 3 of decision 0121 moves the lists of the Dafny model, and the lists of statements and of cases, to `List<T>`. The cases of a `switch` stay a list of their own, and do not become a list of blocks. One generic function adds a list to the end of another list. It replaces the two functions that did this for calls and for contract lines.

## Why

0121 said that a rule that reads statements also reads cases when the cases are blocks. The functions that read cases have about 170 lines in total. A merge saves about 120 of them. But the translator reads cases and statements in different ways. A statement sees the locals of the statements before it, through `spec_scope`. A case sees only the scope of the switch. A merge must keep this difference in `spec_stmts` and in each lemma that follows it, so it can add a defect and it saves little. The cleanup of 0121 makes the core smaller by about 230 lines in total, and not by 700 to 800 lines as 0121 said.

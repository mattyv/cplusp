# 0048: An indirect call counts where it runs, and code in a plain body is plain

Date: 2026-10-07. Status: decided. Amends 0047 on nested functions, and the row `function_pointers`.

## Decision

- **An indirect call counts where it runs.** The row `function_pointers` judges the call too, not only the spelling of a type. Verified code can run an indirect call, itself or through code that the file does not write. When the lowered form cannot name each target, the call is a finding of the row, at its line. A virtual call and a table of decision 0037 name their targets. A deduced type spells no pointer, so before this the row did not see the call.
- **A virtual call reaches every override in the module.** This includes an override that the file wrote. It includes one in a class template over a base that it takes as a parameter. A plain override is then refused at the call as well as where it overrides.
- **Code in a plain body is plain.** A lambda or a local class in a plain function is plain. Clang takes no marker on a lambda, and a plain body is out of the gate's view. A lambda or a local class in a trusted body stays verified, as 0047 says.
- **Every function keeps its ends in one file.** The gate refuses one whose first and last token are in two files, of any kind. For a marked function, a macro at an end is refused too, as 0047 says. The message tells the bot to write both ends in the function's own file.

## Why

The review of the 0047 green step found four ways past it. A trusted function gave out a pointer to a plain function with a deduced type, and verified code called it. A class template wrote a plain override that a verified virtual call ran. A local function with its ends in two files took the kind of the trusted body around it. A compile database with two entries for one file merged their places. The fourth is a build, and 0047 covers it already. The first is the row's own hole, and a marked function only showed it. What runs counts, decision 0038.

A lambda in old code is common, and a plain mark says that the code is out of view. To judge it as verified would refuse the old code that the mark sets aside.

## What changes

A check in the lowered form for an indirect call with targets that it cannot name, under the row `function_pointers`. The reach of a virtual call takes each override. The plugin gives a function in a plain body the plain kind. The rule on two files takes every function. The gate runs once for each entry of a compile database. Two lines in the sample pair of `function_pointers` and new lines in the fixtures of markers.

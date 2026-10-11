# 0128: The core checks the flags of the compiler

Date: 2026-10-11. Status: decided. Amends 0022 and 0077.

## Decision

The check of the flags after `--` moves from the shell into the Verus core. The lists of flags and the order of the reasons do not change. The output of the gate and of `prove` does not change.

- The shell gives the core each flag as bytes, and the checks of the config. The core gives the index and the reason of each refused flag. It also says when no flag sets `-std`, and when no flag sets contraction off. The shell makes the sentences, as before.
- The core proves that a run with no refusal has three facts. Some flag sets `-std`, and each `-std` names C++23 or later. The last flag that sets contraction sets it off. No flag changes floating-point results, changes what the compiler reads or reports, or hides a warning that the policy names.

## Why

The proofs assume C++23, IEEE 754 round to nearest and no fused multiply-add. A flag that the check misses can change the program under the proof. Then `prove` can say `ok: proved` for a build that does not keep the contract. Decision 0077 puts each such decision in the core. The user chose this move after the reader of Dafny. The move of the Dafny names, the fourth in the list, waits for the user, because each defect there makes Dafny fail and not prove.

# 0221: A requires line that no input meets

Date: 2026-10-31. Status: decided. Amends 0220. Builds on 0068 and 0165. A function with `//@ requires false` proves for any body. The review of 0220 found the same case through an interface: a final class `Dead` whose `valid()` always gives `false`. Its override proves a contract that cannot hold, under a requires line that no input meets. A function with `requires p.valid()` then proves `result == 42` and returns 0.

## Decision

`prove` keeps `ok: proved` for a function whose requires lines no input meets. This holds for each requires line of each function. That is a free function, a member function, a constructor, an override and a virtual function of an interface. The core, the shell and the plugin get no new check.

## Why

A requires line is a duty of the caller, decision 0068. Dafny checks it at each call in verified code. So the proof of such a function is true as stated, and no verified code can call it. A call of it gives `a requires line of the callee may not hold.` at the call line. Only code that the gate does not check can run such a function. In that code each requires line is an assumption, whether it is `false`, `p.valid()` or `x > 1000000000`.

For 0220, the check of an override can pass on a class whose `valid()` never holds. The axioms stay true, because each value of the interface can be a value of that class. No verified code can call through the interface on that class. A second class whose `valid()` can hold must keep the contract in its own check.

The review measured three other ways and did not take them:

- A proof that each requires line can hold. The examples have 120 requires lines, and about 70 of them read `valid()` of a class or an interface. Dafny can name no value of the type of an interface. So for a parameter of an interface, the proof fails on correct code.
- The Dafny flag `--warn-contradictory-assumptions`. It finds both cases, but the lemma `trunc_div_size` of the prelude fails with it. On the 61 examples that translate, it gives 54 warnings in 5 files, and none of them is a defect. Most are in proof text that the translator writes. It also adds a second Dafny run to each `prove`.
- A note that does not change the exit code. It has the same false warnings, and the bot cannot act on most of them.

The flag is the upgrade path if the gate must find such a requires line later. First the prelude lemma must pass with it, and the translator must stop writing the steps that it warns on.

## What changes

The skill tells the bot that a requires line is a duty of the caller. `docs/soundness.md` says where the risk is: the requires lines of the functions that unverified code calls. One test holds the behaviour, so that a later change needs its own decision.

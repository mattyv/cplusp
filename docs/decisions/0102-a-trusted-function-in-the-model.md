# 0102: A trusted function in the model

Date: 2026-10-09. Status: decided. Builds on 0003, 0039 and 0047, the markers.

## Decision

- A function with the marker `CPLUSP_TRUSTED`, declared or defined, is a Dafny method with its contract and no body. The method has the attribute `{:axiom}`, so Dafny takes its ensures lines as given. The translator does not read a body that the function has.
- A call of a trusted function proves from its contract alone, as each call does. A trusted member function is never pure, so a contract cannot call it, decision 0090.
- A function with no body and no marker still has no method. A call of it is refused, as before.
- `cplusp prove` names each trusted function of the file that the model holds, on a line before the verdict: `Trusted: FILE:LINE: NAME: REASON`. `Trusted:` is a fixed prefix, as `Not provable:` and `Not proved:` are. `ok: proved` then means that each verified function is proved, and that the proof rests on these contracts.
- Whether the contract of a trusted function holds is the claim of its author, with the reason the marker gives. The gate refuses a trusted function with no contract or with no reason, decision 0047.

## Why

Eight examples call a trusted function, such as a read of a hardware register or a call through a function pointer. The plan says that a proof ends at trusted contracts, and that each run lists them with their reasons. The model did not hold them, so each caller was refused.

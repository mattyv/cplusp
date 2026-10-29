# 0207: A variant whose alternative cannot be assigned

Date: 2026-10-29. Status: decided. Amends 0206. The review of 0206 found one more quiet pass. The reviewer decided the fix.

## Decision

Each alternative of a variant must also be move-constructible and move-assignable, next to the two rules of 0206. A struct that deletes its copy assignment fails this rule. Any other variant keeps the sentence of its type: `<type>: the translator has no rule for it yet.`

## Why

libstdc++ keeps the value of a variant on a change to a new alternative only when two things hold. Each alternative is trivially copyable and at most 256 bytes, as 0206 says. And each alternative can be move-constructed and move-assigned. Otherwise it destroys the old value first, and a throw then leaves the variant with no value. The review showed such a variant: its alternative is a plain struct with `operator=` deleted. The plan states the trusted assumption with this rule too.

## What changes

The plugin checks that each alternative can be move-constructed and move-assigned. It also reads a copy of a variant argument only through the copy or the move constructor of its type. The fixture of 0206 gets one more line.

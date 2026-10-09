# 0111: A parameter on a modifies line is no global

Date: 2026-10-09. Status: decided. Amends 0035.

## Decision

A name on a modifies line or a reads line that names a parameter of the function is that parameter, as in C++ scope. The gate does not read it as a global with the same name. A call of the function then changes no global by that name.

## Why

The review of 0108 found a correct program that the gate refused. A function writes its reference parameter `count`, and the file also has a global `count`. The gate read the modifies line as a write to the global, and it refused each caller that did not list `count`. When the caller listed it, the translator refused the caller, because `count` is no reference parameter of the caller. No program could pass both.

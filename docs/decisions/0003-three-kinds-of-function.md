# 0003: Three kinds of function

Date: 2026-10-03. Status: decided.

## Decision

Verified: gated and proved. Trusted: a contract without a proof, with a reason. Plain: ordinary C++ with no contract. Verified code may call only verified or trusted code. The bot may mark a function trusted or plain with a one-line reason. New functions are verified by default. Edited functions keep their kind.

## Why

The bot must be able to write non-provable code when it has to, and the design must still push toward provable. Visible exceptions beat blocked ones.

## What changes

Three markers. A rule that verified code calls only contracted code. Reports that count verified, trusted and plain. Whether a human must approve new markers is open.

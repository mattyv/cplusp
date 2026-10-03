# 0022: The baseline is C++23

Date: 2026-10-03. Status: decided. Amends 0021, which named C++20.

## Decision

Verified code is C++23 or later. The gate refuses a build with a `-std` below C++23, or with none. The tests, the samples and the battery compile as C++23. The pinned compiler, clang 18, handles C++23.

## Why

The facts the proofs rest on were fixed in C++20, and a later standard never takes them back. C++23 adds `std::expected`, which the subset already lists. It is 2026, and nothing in the project needs the older baseline.

## What changes

Every `-std=c++20` in the tests becomes `-std=c++23`. The flag refusal of decision 0021 names C++23. The battery can cover `std::expected`.

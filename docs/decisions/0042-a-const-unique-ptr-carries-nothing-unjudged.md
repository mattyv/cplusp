# 0042: A const unique_ptr carries nothing unjudged

Date: 2026-10-07. Status: decided. Amends 0041, which counted every handle as a way to write.

## Decision

A const `std::unique_ptr` carries no way to write. A const lvalue of one is a read where it stands, so a function may take it by const reference. A `shared_ptr`, a `weak_ptr` and a `reference_wrapper` still carry one.

## Why

A `unique_ptr` cannot be copied, so a const one cannot leave by a copy. Every use of what it owns is a source of its own, because the handle is const, and the check judges that use where it is written. The example `tree_unique_ptr` passes `root->left` to a function that takes `const std::unique_ptr<Node>&`, which is the shape a recursive tree has. Decision 0041 refused it. A `shared_ptr` copies, and the copy writes, so it stays a way to write.

## What changes

The const-handle check counts a const `unique_ptr` as carrying nothing. The example `tree_unique_ptr` is the pin.

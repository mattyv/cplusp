# 0038: What runs counts, and only the compiler reads the source

Date: 2026-10-07. Status: decided. Amends 0025, which made a pragma a finding of the gate's own preprocessor run. Amends 0037, which kept that run for pragmas. Follows a fifth outside review, of 5d01d66.

## Decision

The gate judges what the compiler runs, as the compiler reads it. Three rules follow.

- **Only the compiler reads the source.** The plugin reports every pragma from the preprocessor's callbacks. It reports every line directive that way since decision 0037. The gate parses no compiler output that holds source text. The NOLINT scan reads the files of the compiler's dependency list, which the compiler makes from its include graph. The gate's preprocessor run goes. The gate refuses a flag that changes what the compiler reads or reports, such as `-E`, `-M` or `-###`.
- **Every operation that runs counts.** A check that asks what an expression does visits every node that runs where the expression is written. That is its children, a default argument, a default member initializer, and the capture initializers of a lambda. It is not the body of the lambda. A call's effect always comes from the table of decision 0037. The short list of std names that change nothing excuses their parameters only, never their code. A copy that `make_pair` makes runs the copy constructor, and that counts.
- **Const reaches through a return.** A function may not return a non-const reference, pointer or span that reaches through a const handle. Else the caller writes through it, and the call shows no handle.

## Why

The fifth outside review found four ways past 5d01d66. Each was a place where the gate read something other than what runs. A raw string held a fake line marker, and the gate's scan of the preprocessor output took it for a real one. The scan then missed the real `system_header` pragma in the header. The sequencing check skipped a default member initializer and the capture initializer of a lambda, and both run where they are written. A list of std makers that change nothing skipped the table, though `make_pair` copies its arguments. A function returned a mutable reference through a const handle, and its caller wrote through it.

The first is the shape that decision 0037 closed for line directives: a second reader of the text. The callbacks of the preprocessor and its dependency list are the compiler's own reading, and a raw string cannot reach them. The other three are one rule. An operation that runs adds its effect, wherever the tree puts it.

## What changes

A plugin check for pragmas, with the messages the gate gives today. The gate's preprocessor run and its marker reader go. The sequencing check walks one function that visits what runs, for its changes and for its reads. The const-handle check reads returns. The limit of the row `evaluation_order` says what the std names excuse. A pin for each finding.

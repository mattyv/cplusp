# 0058: The second slice: locals, integral casts and calls

Date: 2026-10-08. Status: decided. Amends 0057 on the second slice.

## Decision

- A local has one name, a type of the subset and a start value. One declaration is one statement. A local with no start value, or two names in one declaration, has no rule yet.
- Each name in a function is declared once. A parameter and a local with the same name, or two locals with the same name, are refused at the second declaration. The model names a variable by its name, so a second declaration would read as the first.
- An integral cast between two integer types of the subset is a cast in Dafny, such as `(x as int64)`. Dafny proves that the value fits the new type. C++ wraps a value that does not fit an unsigned type, and C++20 wraps a narrowing cast. The model refuses to wrap: code that relies on the wrap does not prove. A cast between `bool` and a number has no rule.
- A braced value of one scalar, such as `int64_t{a}`, is that value. A braced start value cannot narrow, so the compiler already checked it.
- A call has a model when it names its function directly. That function must be a plain function with a definition in view and a signature of the subset. A member call, an operator call, a call through a pointer and a call to a template have no rule yet.
- A call stands alone: it is the full value of a `return` or the full start value of a local. Its arguments hold no call. Nothing in the subset writes, so the order in which C++ reads the arguments cannot change the result.
- The plugin names each function by its qualified name and the place of its definition. An overload, a function of the same name in another namespace and a declaration with no definition are each a different function. The shell gives each one a different Dafny name.
- A function whose signature is in the subset always has a method in the model, so its callers can name it. When its contract or its body is refused, the method has no contract and no body. A method with no contract assumes nothing, so no caller proves more than the code gives. The refusal stays, so the run fails.
- A call to a function with no method is refused at the call.

## Why

`examples/saturating_add` needs locals, casts and a call. The rules above are the least that covers it without a hole. Dafny cannot call a method inside an expression. C++ leaves the order of the arguments open. So a call that stands alone is the simple case. The refusal to wrap costs code that wraps on purpose, and in exchange a cast that loses a value never proves. A refused callee that kept its contract would be an axiom. No body would check it.

## What changes

The core gains locals, integral casts, braced values and calls. It also gains a model for each function in the file, and the check that each name is declared once. It proves that each call in a method names a method of the model. The plugin writes the key of each function and of each callee. The shell writes a method with no body for a function whose body is refused. The finding of the review of slice 1, that overloads gave Dafny two methods with one name, is closed by the keys. A function with a contract and no definition is closed by the refusal at the call.

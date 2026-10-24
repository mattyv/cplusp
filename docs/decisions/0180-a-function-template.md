# 0180: A function template

Date: 2026-10-24. Status: decided. Builds on 0036, 0055 and 0058. The example `templates` uses one template at two types. The examples `callbacks`, `crtp`, `stack_template` and `type_erasure` need it later.

## Decision

A free function template with type parameters only is a function of the model for each type that the file uses it at. An instance is the template with its type arguments, as the compiler makes it. Each instance gets the contract of the template. The core reads the contract over the types of the instance and proves each instance alone. An explicit instantiation, as `template int32_t keep<int32_t>(int32_t);`, makes an instance too. A function template of the main file with no instance has no rule, at the line of the function. An instance is a specialization that the file defines, or that a declaration `extern template` names. Overload resolution can make a specialization and then choose another function. That specialization is no instance. Nothing proves the contract of a template with no instance. An explicit instantiation proves it at one type. A declaration `extern template` makes an instance with no body here, so a call of it gets the sentence of a call with no model.

A call of a template calls its instance. A call with an explicit type argument, as `larger<int32_t>(a, b)`, calls the same instance as a call that deduces it. An instance can call another template. That makes an instance of the callee too.

The Dafny name of an instance is the name of the template, then `'of'`, then the Dafny type of each argument. A `'` separates two arguments. So `larger` at `int32_t` is `c_larger'of'int32`, and `first` at `int32_t` and `bool` is `c_first'of'int32'bool`. Two functions of the model can still get one such name. Examples are two templates of one name at one type, `long` and `long long`, and a static member function `larger::of::int32`. Then each gets `'1`, `'2` and on, as an overload does. The shell counts the whole name with its types.

A line of a template belongs to each instance. A block is the line, the sentence and the contract lines under it. When more than one instance gives one block, the shell prints it as many times as one instance gives it. Two different sentences on one line both print, as "the value may not fit int32_t." and "the value may not fit uint32_t."

These forms have no rule:

- a member function template, at the line of the function. The sentence is "a member function template: the translator has no rule for it yet."
- a function template of the main file with no instance, at the line of the function. The sentence is "a function template with no instance: the translator has no rule for it yet."
- a form in the body of an instance that has no rule, at its line in the template. The instance then has no contract for its callers, as each refused function has. So a caller can fail to prove.
- a parameter or a result with a type that is no type of the model, as `Box<int32_t>`, at the line of the function. It has the sentence of that type.
- any other type argument with no Dafny name, at the line of the function. Examples are `std::vector<int32_t>`, and a `Box<int32_t>` that no parameter holds. The sentence is "a type argument with no Dafny name: the translator has no rule for it yet."

A caller of such an instance gets the sentence of a call with no model.

The gate already refuses a specialization and a template parameter that is not a type, in the row `templates` of the policy. A class template is a later decision.

## Why

A template is not code until the compiler makes an instance. The instance is code with ordinary types, and the model already has the words for it. The contract is the same for each instance, but the proof is not. A sum that fits `int64_t` can overflow `int32_t`. So each instance needs its own proof.

## What changes

The plugin writes each instance of a free function template as a function, with the contract of the template and the lines of the template. The shell prints the Dafny name of an instance. The core needs no change. Three fixtures follow the form of 0178. The example `templates` proves, and its file `example.dfy` shows the instances.

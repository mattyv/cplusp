# 0188: A class template

Date: 2026-10-25. Status: decided. Builds on 0089, 0094, 0096 and 0180. Amends 0180 on a type of a class template, as `Box<int32_t>`, and 0089 on a member function template of an instance. The examples `crtp` and `stack_template` are class templates with type parameters only.

## Decision

A class template with type parameters only is a struct of the model for each type that the file uses it at. An instance is the template with its type arguments, as the compiler makes it, with a definition. A type that only a declaration names has no definition. Its fields have the types of the instance. The core reads it as any other struct or class.

A member function of an instance is a member function of the model, with the contract of the template. The core reads the contract over the types of the instance. It proves each instance alone, as 0180 does for a function template. The compiler makes the body of a member function only where the code calls it. A member function that only a contract calls has no body then. A call of it gets the sentence of a call with no model. An example is `a call to Stack<int>::valid, which has no model in view.` Nothing proves the contract of a member function that no instance makes, as 0180 says for a function template. So such a member function with a contract has no rule, at the line of the function. The sentence is `a member function with no instance: the translator has no rule for it yet.` An explicit instantiation, as `template class Stack<int32_t>;`, makes the body of each member function. So write one for each instance that the file uses.

The Dafny name of an instance is the name of the template, then `'of'`, then the Dafny type of each argument, as 0180 says. So `Stack<int32_t>` is `S_Stack'of'int32`, and its member function `push` is `c_Stack'of'int32'push`. Two names that are the same get `'1`, `'2` and on, as an overload does.

A line of the template belongs to each instance. When more than one instance gives one block, the shell prints it as many times as one instance gives it, as 0180 says.

These forms have no rule:

- a class template of the main file with no instance, at the line of the class. The sentence is "a class template with no instance: the translator has no rule for it yet."
- a type argument with no Dafny name, as `std::vector<int32_t>`, at the line of the class. The sentence is that of 0180, "a type argument with no Dafny name: the translator has no rule for it yet."
- a member function template of a class template, with the sentence of 0180. The instance stays a struct of the model. A call of the member function template gets the sentence of a call with no model.
- a form in the body of a member function that has no rule, at its line in the template.
- a member function of an instance that is no struct of the model, as one with a dependent base or a `std::map` field. It gets the sentence of a member function of any class that is no struct of the model. That sentence is `CXXMethodDecl: the translator has no rule for it yet.`

The gate already refuses a specialization and a template parameter that is not a type, in the row `templates` of the policy.

## Why

A class template is not code until the compiler makes an instance. The instance is a class with ordinary types, and the model already has the words for it. The contract is the same for each instance, but the proof is not, as 0180 says for a function template.

## What changes

The plugin writes each instance of a class template as a struct, with its fields and its member functions, under its Dafny name. The core marks a member that has no function of the model. A contract that calls it then gets the sentence of a call with no model. This holds for each struct, also for a const member function of a plain struct that the file only declares. The shell prints the name of each instance. Three fixtures follow the form of 0178. The fixture of 0180 drops its refusals of `Box<int32_t>`, because it is now a type of the model. The examples `crtp` and `stack_template` need more rules than this one, so later decisions make them prove. `crtp` calls a pure member function of a field in a pure body. `stack_template` writes a vector field with `push_back` and gives a reference to an element.

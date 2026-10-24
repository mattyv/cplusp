# 0178: A struct with a destructor

Date: 2026-10-24. Status: decided. Builds on 0089, 0094, 0096, 0108 and 0173. Amends 0173 on a member function that lists a global. The examples `classes_raii` and `raii_handle` have a guard and a handle whose destructors release what their constructors acquired.

## Decision

A struct of the subset can have a destructor with a contract. The destructor is a method, `c_Guard'dtor`. It takes the object and the globals that it lists, and gives them back, as a member function that writes its object does, decision 0096. The object dies after the call, so no statement reads the value that comes back. Its contract reads the fields and the const member functions of the object, and `old()` of a global.

The destructor runs where C++ runs it. A block is the body of a function, a branch of an `if`, the body of a loop or a case of a `switch`. A bare block `{ ... }` is a block too. At the end of a block, each local of the type that the block declares dies, in the reverse order of the declarations. Before a `return` or a `return;`, the translator first computes the value of the return. Then every live local of the enclosing blocks dies. A `return` whose value runs a call only sometimes, decision 0177, sets the result in each branch, and then the locals die. Each destructor call has the line of the statement where its local dies: the return, or the last statement of the block.

A value of a struct with a destructor stays in its block. These forms have no rule:

- a `return` of such a local,
- a parameter of the type, by value or by `const` reference, at the line of the function,
- a field of the type, at the line of its struct,
- a local whose start value is not a call of a constructor of the type,
- a value of the type that is not a name, such as a call that gives the type or a brace list `Lock{5}`,
- a sequence, an optional or a `unique_ptr` of the type, at the line of its declaration.

The value of a `return` that is a brace list of the type is the result itself, as in the body of a constructor. It is no temporary, so it has a rule.

The model cannot tell a parameter by value from a parameter by `const` reference, so neither has a rule. No example needs one. Each of these forms gets one sentence. It is "a copy of a struct with a destructor: the translator has no rule for it yet."

A `for` with a local of the type in its head has no rule. The plugin writes it as an unknown statement.

A call of a destructor in code, such as `g.~Guard();`, has no rule. C++ runs the destructor again at the end of the block. Its sentence is "a call of a destructor: the translator has no rule for it yet."

A struct whose destructor has no contract has no rule as a local. Its sentence is "a destructor with no contract: the translator has no rule for it yet."

A deleted copy or move constructor or assignment is a declaration. It changes nothing.

A member function that writes its object, a constructor or a destructor can list a global on a `reads` or a `modifies` line. The global is an implicit parameter after `this` and the parameters, decision 0173. A `const` member function or a virtual function that lists a global keeps the refusal of 0173. The function twin of a `const` member function takes no global yet, and no example needs a virtual function that lists one. Its sentence is now "a const or virtual member function that lists a global: the translator has no rule for it yet."

## Why

The two examples acquire in a constructor and release in a destructor. The count of open handles is a global. The constructor of a guard lists the global, so a member must take a global. The destructor runs at the end of the block. The model must run it there too. Else a caller proves the count from the constructor alone and never sees the release. A copy of such a value would run the destructor twice, once for each copy. So a copy has no rule until a decision gives it one. The destructors run in the reverse order of the declarations, as C++ has it. The hand model in Dafny proves the contracts of the examples in that order. It fails when a model drops a destructor or runs it before the value of the return.

## What changes

The plugin takes a struct with a user destructor as plain. It writes the destructor as a member under the name `~`. It writes a bare block as `Block`. The core gains `Stmt::Block`. It gains the destructor calls at the end of a block and before a return. It gains the two refusals. It keeps the refusal of 0173 only for a `const` member function and a virtual function, with the new sentence. It writes a `for` with a local of a struct with a destructor in its head as an unknown statement. The shell prints the name of the destructor and the two sentences. Three fixtures: `model-dtor.cpp` proves, `model-dtor-wrong.cpp` fails at the named lines, `model-dtor-refuse.cpp` refuses with the sentences. The example `classes_raii` proves. The fixture `model-state-refuse.cpp` now holds a `const` member function that lists a global, and its test keeps the line with the new sentence.

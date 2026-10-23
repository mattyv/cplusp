# 0174: A static member function is a free function with the name of its class

Date: 2026-10-23. Status: decided. Builds on 0090, 0102 and 0173. This is step two of the plan of 0173, for the examples `singleton` and `arena`.

## Decision

A static member function is a free function. Its name is the qualified name as one word: `Tally::bump` is the method `c_Tally'bump`. It takes no object. Its globals are implicit parameters, decision 0173. A trusted static member function is an axiom method, decision 0102.

A static member function with a `reads` line, no `modifies` line and a body of one `return` gets a function twin, `c_Tally'valid'`. The rule is the one for a const member function, decision 0090. The twin takes the globals that the function reads, by value, in the order of the file.

A contract can call the twin. A bare call inside the class, `valid()`, names the static member function of that class. A qualified call, `Tally::count()`, names it from anywhere. The call fills each global parameter of the twin with the global as the line reads it. In a requires line that is the value before. In an ensures line it is the value after. Under `old()` it is the value before. The translator refuses a contract that calls a static member function with a `modifies` line. The sentence is the one of decision 0090: "Tally::bump is no pure member function of its struct."

A struct or class with a static member function is in the table of structs, also when no type names it. Its static member functions are members of the table under their qualified names. Its const member functions stay under their plain names.

A bare call outside the class keeps the sentence of today. The sentence is "valid is no function of the companion file."

A static member function whose contract names a field of the class keeps the sentence of today. The sentence is "n_ in the contract is no parameter."

## Why

The examples `singleton` and `arena` keep their data in static data members and read it through static member functions. Their contracts call those functions, as `valid()` inside the class and `Tally::count()` outside it. With decision 0173 the globals are parameters. So a static member function is a free function with one more thing. A contract inside its class can write its name bare. The qualified name is one id. So a contract never confuses `Tally::valid` with `Pool::valid`. The plain name of a const member stays apart from the qualified name of a static.

## What changes

The plugin writes a static member function with its qualified name and the name of its class, and no `this` parameter. It writes the struct of a class that has a static member function. The static member functions are among its members under their qualified names. The shell reads a bare call in the contract of a static member function as the qualified name of that class. It merges `A::b` in a contract into one name when the text is a global or a static member function. The core finds a static member function by its qualified name in any struct of the table. It fills the global parameters of the twin from the names of the line. Three fixtures: `model-static.cpp` proves, `model-static-wrong.cpp` fails at the named lines, `model-static-refuse.cpp` refuses with the sentences. The examples `singleton` and `arena` prove. The ensures line of `first_block_of_new_frame` in examples/arena puts `Arena::valid()` first, because `used()` requires it.

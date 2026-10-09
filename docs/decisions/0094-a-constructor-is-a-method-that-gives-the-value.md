# 0094: A constructor is a method that gives the value it builds

Date: 2026-10-09. Status: decided. Step 4 of 0089. Amends 0073 on constructors.

## Decision

- A constructor of a struct is in the subset when its member init list gives each field a value and its body is empty. Its model is a method with the parameters of the constructor. It gives the value of the datatype, built from the init list in the order of the fields.
- The plugin writes the result type of a constructor as `This` of its struct. A result of `This` is the object that the constructor builds.
- In a contract of a constructor, a name that is no parameter and is a field of the struct is that field of `result`. A call of a pure member function, as in `valid()`, passes `result`, decision 0090.
- A struct that holds a sequence still has no constructor in the subset, because its result would be such a struct, decision 0076.
- In code, `S s(a)`, `S s{a}` and `return S(a)` call the constructor, under the rule that a call stands alone, decision 0058.
- A struct with a constructor is still plain, decision 0089. These still have no rule: a field with a default value, a constructor with a body or one that leaves a field out, a delegating constructor, and a destructor.

## Why

The classes of the examples set their fields in a constructor and state the result with `valid()`. A constructor with only an init list computes a value, as a function does. The model was checked by hand in Dafny with a counter and a caller.

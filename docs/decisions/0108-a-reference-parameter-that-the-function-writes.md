# 0108: A reference parameter that the function writes takes a value in and gives it back

Date: 2026-10-09. Status: decided. Amends 0074. Extends 0096 from the object to the parameters.

## Decision

- A parameter of type `T&` is in the subset when `T` is a scalar type or a struct of the file. Its type in the model is `Mut(T)`. `const T&` stays a value, as before.
- The line `//@ modifies a, b` above a function names the reference parameters that the function writes. The translator refuses any other name with `NAME on the modifies line is no reference parameter.`
- A reference parameter on the modifies line takes its value in and gives it back, as the object of 0096 does. The method has the parameter `x` and the result `x'`. The body starts with `x' := x`, and reads and writes `x'`.
- Each reference parameter must be on the modifies line. If the line does not name one, the translator refuses the function. The sentence is `x is a reference parameter that the modifies line does not name.` A function that only reads a value takes it by value or by `const T&`.
- In the body, `x = e`, `x op= e`, `++x` and `--x` write the parameter. For a struct, `x.f = e` writes a field.
- In the contract, a requires line reads the value before the call. An ensures line reads the value after the call, and `old(x)` reads it before the call.
- A call writes back each argument at the place of a written reference parameter, and the object of 0096. Each such argument is a local, or a written reference parameter of the caller. As a statement, `f(a, b);` is `a, b := f(a, b);`. As the start of a local, the call sets the local and the arguments. Any other argument there has no rule yet.
- Three sentences change, because the translator now also writes a reference parameter:
  - A write to a parameter by value: `NAME is a parameter. The translator writes only a local or a reference parameter.`
  - A call that writes back to any other place: `the call writes a value back, and the translator writes back only to a local or a reference parameter.`
  - A call out of place: the sentence ends `It takes a call that writes a value back or gives no value only alone.`
- The results of a method are in this order: `result`, then `this'`, then the written reference parameters in the order of the parameters.

## Why

Twelve examples use a reference parameter, and three stop only there: `lvalue_references`, `raw_memory_ops` and `evaluation_order`. A function that writes a reference parameter is a function from the old values to the new ones. So the value model of 0029 still holds, and the object of 0096 is the same idea for one parameter. The gate refuses two references to one object in a call, decision 0033. So each written argument is a separate value.

The modifies line is already the line that the examples write. It also tells the reader what the function writes. A reference that the function only reads has a better type, so the translator does not need a third view of a parameter.

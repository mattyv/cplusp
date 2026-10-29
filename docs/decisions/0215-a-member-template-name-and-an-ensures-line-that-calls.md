# 0215: A member template name and an ensures line that calls

Date: 2026-10-29. Status: decided. Amends 0212 and 0213. The review of 0211 to 0213 found three defects. A contract that called a name of a member function and of a member function template proved with the wrong contract. Two functions whose ensures lines call each other did not prove. A static member function template got the sentence of a bad name.

## Decision

- A member function template counts as an overload of its name, decision 0210. So the plugin refuses a contract that calls that name, with the sentence of a function that is not pure. A contract cannot call an instance of a member function template.
- A static member function counts in the same way. A static member function can share its name with a member function template or with one more static member function. Then the name is an overload, and a contract that calls it gets the same sentence. The shell also refuses a contract call of a static member function that the table of members does not hold.
- The function of 0213 keeps only the ensures lines that call no function. A line that calls a function stays on the method.
- A static member function template has no rule yet. It gets the sentence `a member function template: the translator has no rule for it yet.`

## Why

A contract call names a member, not an instance. With a template of the same name, the call can be one of two functions, so the model cannot pick one. A function can call another function in an ensures line, and that function can call the first in its own line. Then Dafny cannot show that the two end. The method has no such problem, because a method is not part of the functions that Dafny unfolds. A static template is not a member of an object, so the rule of 0212 does not apply.

## What changes

The core drops each ensures line that calls a function from the function of 0213. The plugin counts each member function template name with the names of the class, and keeps the template sentence for a static member function template. Five fixtures hold the cases.

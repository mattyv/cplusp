# 0186: A tree that the code builds

Date: 2026-10-24. Status: decided. Builds on 0029, 0075, 0142, 0167 and 0171. Amends 0171 on a parameter that moves, and on a return with no `std::move`. The example `tree_unique_ptr` makes a node with `std::make_unique`, sets its fields through the pointer, and moves its children in.

## Decision

`std::make_unique<S>()` with no argument, of a plain struct `S`, gives a pointer to a new value of `S`. Each field of the value has its start value:

- A field of an integer type or of `bool` starts with the value of its default member initializer. The initializer must be a constant expression.
- A field `std::unique_ptr` starts null when it has no initializer, or when its initializer is `nullptr`.

A field of any other type, such as an enum, keeps the sentence of today. So do a scalar field with no initializer and an initializer that is not a constant expression. An initializer that overflows or writes a name is not a constant expression. That sentence is `a call to std::make_unique<S>, which has no model in view.`

`n->f = e` writes the field `f` of the value that `n` owns. Here `n` is a local `std::unique_ptr<S>` of a plain struct `S`. Dafny reads it as `n := Some(n.value.(f := e));`. Dafny proves that `n` is not null there, with the sentence of 0075. The value `e` can be `std::move(x)` of a local `std::unique_ptr`, as at the start value of a local, decision 0171. Then `x` is null after the statement. The statement reads `n`, so `n` cannot move in it. The gate refuses that move, and the core refuses it too, with the sentence of 0171. The gate also refuses a write through a parameter `const std::unique_ptr<S>&`, because it is a const handle.

A parameter `std::unique_ptr<B>` by value that the body moves outside a `return` is a local of the function in the model. It starts with the value of the argument. So it moves in each place where a local moves, and it is null after the move. C++ makes a moved `std::unique_ptr` null, so the code can test it. It follows each other rule of a local `std::unique_ptr` too. A contract reads the parameter as its value on entry, as before. This replaces the rule of 0171 that a parameter moves only in a return.

`return x;` of a local `std::unique_ptr<S>` of a plain struct `S`, or of such a parameter by value, moves `x`, as C++ does. It gives the value of `x`, as `return std::move(x);` does. This replaces the rule of 0171 that such a return has no rule yet. A `std::unique_ptr` of an interface keeps the refusal of 0168 for a return with no `std::move`.

These have no rule yet:

- a write through a parameter by value that the body does not move, or moves only in a `return`. The sentence is that of 0108, `p is a parameter. The translator writes only a local or a reference parameter.`
- a compound assignment through the pointer, such as `n->f += e`, and a write to a field of a field. These keep the sentence of today.
- `return nullptr;`, and an assignment of one `std::unique_ptr` to another, as before.

The sentence for a move in any other place now names the field write. It is `a std::move of a std::unique_ptr has no rule here. It has a rule only in a call that stands alone, the start value of a local, a return or a field write.`

## Why

A tree of `unique_ptr` nodes is the common form of an owned recursive structure. The model already reads it as an Option of a recursive datatype. The code only needs to make a node, set its fields and give it away. A parameter by value is a local object in C++. The model now reads it the same way, so a move of it is a move of a local.

## What changes

The core gives each parameter that the body moves outside a `return` a local of the same name. The body is a block that starts with these locals. Dafny reads the name in the block as the local, and the contract reads the parameter. The core reads a field write through a local `std::unique_ptr` as a write of the value that it owns. The plugin writes `std::make_unique<S>()` as the value of `S` with the start value of each field. It writes the field write through a local, and `return x;` of a local `std::unique_ptr` of a plain struct as a move of `x`. The shell prints the new statement. Three fixtures follow the form of 0178. The fixture of 0171 drops its refusal of a parameter that moves in a call. The example `tree_unique_ptr` gets its companion file, with the lemma `SumBound`, and two `apply` lines of 0167 in `sum`. The example `tree_unique_ptr` proves.

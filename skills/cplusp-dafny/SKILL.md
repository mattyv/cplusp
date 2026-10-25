---
name: cplusp-dafny
description: Develop and review C+P subsystem contracts, composition proofs and hand-written Dafny models. Use when planning verified C++ changes, specifying existing code, generating or challenging formal specifications, reviewing proof scope, or modelling C++ behavior in Dafny. Use the specification-review workflow for Verus core contracts too.
---

# Writing Dafny for C+P

The divergence rules below come from cases in `divergence/dafny/cases/`. The case shows the naive model, the divergence, and the mitigation. Follow the rules. When a construct has no rule, stop and write the case first. For the right way under each row the policy allows, read `examples/<row>/`: the C++ with its contract, and the Dafny for it.

## Whole-program development
For existing code, follow the "Specify existing code" section of the reference below before generating contracts.
Read [Generate and challenge specifications](references/specification-review.md) when generating or reviewing contracts, or repairing proofs. Apply its fixed-contract mutation checks, input-domain checks and outcome reporting. Keep the reviewer and coder roles. Use Verus syntax for the Rust core and the current C+P translation rules for C++.
Read [the research report](../../docs/research/formal-verification-llm-coding-report.md) and [the FAQ](../../docs/formal-proof-faq.md) for proof scope and evidence.
Start top-down with requirements and contracts. Build code and proofs together in small increments.
1. Select one feature. Define its outputs, state changes, failure behavior and allowed inputs.
2. Define the state invariants and initialization guarantees the feature needs.
3. Derive component contracts before implementing their bodies.
4. Check composition early: establish each callee's preconditions and derive the feature's result from its guarantees.
5. Check a difficult operation early against the current translator slice.
6. Implement and prove small increments. Helpers often come first, but use the order that tests the design soonest.
7. Verify initialization, relevant bodies and public entry points. Recheck composition with the completed implementations.
8. Run executable tests, translation regression cases and all relevant proofs after changes.
9. Report guarantees, bounds, trusted dependencies and unproved obligations.
A caller proof that relies on an unimplemented helper's contract is conditional on that helper satisfying the contract.
Keep that obligation visible until its implementation verifies. Do not report the feature as fully proved while it remains open.
Dafny abstract interfaces can support this design check. They do not add support for an unsupported C+P construct.
Review contract corrections as you learn. Follow the repository's reviewer role before changing a reviewed requirement or contract.

Example: sort, then search. Require sorting to preserve all input elements, including duplicates, and establish the search's ordering precondition.
Use the search guarantee and element preservation to establish membership in the original input.
Check this composition before choosing a sorting algorithm. Prove both implementations before claiming the complete feature.

Try to break each contract before you trust it. Write deliberately wrong bodies, such as an empty result, a missed update or wrong handling of duplicates, and check that the contract rejects each one. Show that intended inputs satisfy the preconditions. These checks find weak contracts. They do not prove that a contract is complete.
Build the implementation and its proof together, in small increments. Prove each increment before you build on it. When a proof gets hard, change the data structures or the helper boundaries, and keep the reviewed contract.
Treat a plan as implementation guidance and a formal contract as a machine-checkable requirement.
Do not weaken contracts, restrict valid inputs or add assumptions merely to make proofs pass.
Report requirement changes and any code excluded from verification.
Describe each stateful component's input and output State values. Specify changed fields and preserve the others.
Check aliasing against C++ rules before using the value model. Use stable module contracts to hide implementation details.
For loops, prove invariant initialization, preservation, checks inside the loop and the result at exit.
Prove termination with a valid decreases measure when required.
Keep ghost calculations and lemmas separate from executable behavior. They must not silently replace C++ computations.
Validate arithmetic types, promotions, casts, control flow and state updates against the C++.
Distinguish hand-written models from automatic translation. These rules include features beyond the current translator slice.
Check the latest numbered decisions before claiming translator support. Unsupported automatic translation must remain a refusal.
Do not substitute a hand-written model and report the C++ as automatically verified.
Report translation acceptance, proof outcome and executable test outcome separately.
A successful model command is not a successful proof. A Dafny proof needs faithful translation to establish C++ behavior.
Use the report's pilot method to measure correctness, time and cost.
Treat SPARK guidance as an engineering method, not an LLM performance measurement.

## Contract lines that the translator reads

This list is true at decision 0186. Read the later decisions before you rely on it.
`cplusp prove` translates the C++ and the `//@` lines to Dafny, and runs Dafny. It says `ok: proved`, or `Not proved: FILE:LINE: sentence` for a proof that fails, or `Not provable: FILE:LINE: sentence` for a form that has no rule.

Where each line goes:
- Above a function: `requires`, `ensures`, `modifies` and `decreases`.
- Above a loop: `invariant` and `decreases`. A loop line reads the variables in scope at the loop, decision 0062.
- Above a range-for: `index i`, which names the count of the elements before the current one, decisions 0143 and 0144. The name must be new in the function. The translator adds `i <= v.size()` and, with no decreases line, `v.size() - i`.
- Above a statement in a body: `assert E` and `apply L(a, b)`, decision 0099. `L` is a lemma of the companion file.

What a contract expression can hold:
- The parameters, `result`, and `old(x)` in an ensures line, decision 0096. `old` wraps the whole read: write `old(v[j])` and `old(v.size())`, not `old(v)[j]`. The arithmetic is on exact integers, so a contract cannot overflow.
- `&&`, `||`, `!`, `==>`, `c ? a : b`, `forall i :: ...` and `exists i :: ...`.
- `v.size()`, `v[i]`, `v[i..]`, `v[..j]` and `v[i..j]` of a sequence, and `o.has_value()`, `o.value()`, `*o` and `o->f` of an optional, decisions 0131 and 0137.
- `p == nullptr`, `p != nullptr`, `*p` and `p->f` of a pointer to const or a unique_ptr, decisions 0140 to 0142. Two pointers do not compare.
- Hex literals, `true`, `false` and a character such as `'0'`, decision 0106.
- A decimal with a point, such as `150.0` or `0.5`, is that real, and `std::isfinite(x)` reads a `double`, decision 0150. `|e|` is the absolute value of a real, and `eps`, `eta` and `DBL_MAX` are words, decision 0154. The translator refuses a contract line with one of these words when C++ finds a name of that spelling from the function, decision 0158. A whole number next to a real is that real, so you can write `2 * eps`, `DBL_MAX / 4` and `0 <= x <= 1`. An integer name or field next to a real is that real too, such as `f.raw / 1000.0`, decision 0159. `|e|` of an integer is its absolute value. It is an integer operation, so next to a real it does not read as a real.
- A `constexpr` integer or `double` constant of the file, when C++ finds it from the function, decisions 0106, 0107 and 0158. A `double` constant is exact when its value is `m / 2^p` with `p` up to 63, such as `0x1p-30`. A contract cannot write a hexadecimal double, so give it a name.
- An enumerator such as `Kind::Small`, decision 0109.
- A pure `const` member function, and a function or predicate of the companion file, decisions 0079 and 0090.

The modifies line:
- It names each non-const reference parameter (`T&`) that the function writes, and nothing else, decisions 0108 and 0110. The translator refuses a function with a reference parameter that the line does not name.
- A function that only reads a value takes it by value or by `const T&`.
- Each `double` parameter needs `std::isfinite(x)` as a part of a requires line, joined by `&&`. A trusted function that gives a `double` needs `std::isfinite(result)` in an ensures line. The model has no NaN and no infinity, decision 0150.
- `+`, `-`, `*` and `/` on a `double` are one rounding each, `fadd` to `fdiv` of `Double.dfy`, decision 0154. Each needs a bound in the contract, such as `requires |a * b| <= DBL_MAX`, and a division needs `b != 0.0`. The translator refuses `++`, `--` and `%` on a `double`. An integer converts to a `double` with no rounding up to 2^53 in magnitude, decision 0159. So a conversion of an `int64_t`, a `uint64_t` or a `size_t` needs `static_cast<double>` in the code and a bound in the contract. An integer of 32 bits or fewer needs neither. A `double` does not convert to an integer.
- Write the bound on the exact result itself, `|a * b| <= DBL_MAX`. Dafny does not find it from bounds on `a` and `b`. A bound on the result also needs the error: `|result| <= 2.0` does not follow from `|a| <= 1.0 && |b| <= 1.0`, but `|result| <= 2.0 + eps * 2.0 + eta` does.
- A bound on a double result reads `ensures |result - a * b| <= eps * |a * b| + eta`. `prove` prints an `Axiom:` line when the proof rests on the rounding axiom.
- A `std::vector<T>&` on the line takes its value in and gives it back, decision 0145. In the body, `v[i] = e` writes one element, and `v.push_back(e)` adds one at the end, decision 0148. Neither `i` nor `e` holds a call. `v[i] += e`, `emplace_back`, `pop_back`, `resize`, `clear` and passing `v` on to a `std::vector<T>&` have no rule yet.
- A vector of a plain struct is a sequence of its datatype, decision 0163. A function can give a `std::vector<T>` by value, and a contract reads `result.size()` and `result[i]`. A local can take the vector that a call gives. A contract has no `multiset`, so it names a predicate of the companion file.
- A local `std::vector<T> x = v;` of integers is a copy of a vector in scope, decision 0160. The body can write `x[i] = e` and `x.push_back(e)`, and the vector of the caller stays as it was. A local vector with no initial value, from a list, from a call or from `std::move` has no rule yet. Neither has a local `std::span`, a vector of a struct or of bool, or a call that passes the local by reference.
- `std::sort(v.begin(), v.end())` sorts a local vector or a vector by reference of integers, decision 0161. After it, `v` has the same elements and the same length, and no later element is below an earlier one. A fact about the old vector, such as its smallest element, needs a lemma of the companion file with `//@ apply`. The lemma reads `SortedBy` and `multiset`. `prove` prints an `Axiom:` line for the contract of the sort. With a comparator lambda `[c](T a, T b) { return e; }` of the element type, the sort uses that lambda, decision 0162. Dafny proves that the comparator is a strict weak order on every value of `T`, and `prove` says `the comparator may not be a strict weak order.` when it cannot. A comparator that reads an index or divides must hold for every value, not only for the values in the vector. A sort of any other form has no rule yet.
- An interface is a class with no field and no base, decision 0165. Its members are pure virtual `const` functions and a destructor `= default`. A class over it must be `final`, and each override must be a pure member function with the same parameters and result. A parameter `const B&` reads `s.f(a)` with the contract of `B::f`. `prove` checks each override: it may require less and promise more, never the other way. A failure says `the override may require more than B::f.` or `the override may not keep the promise of B::f.` A requires line of an override that reads a field never passes. A call `s.B::f()` and a body of a pure virtual function have no rule yet. A pointer, a local or a result of an interface type has none either.
- A contract of an interface can call a virtual function of it that comes above, such as `valid()`, decision 0166. A caller can read `s.valid()` and `s.f(a)` of a parameter `const B& s`, and two calls with the same arguments give the same value. A final class goes to a parameter `const B&`, and the caller knows the value of each call from the override. `this->x` reads `x`. A pure virtual function that gives no value has no rule yet.
- `//@ apply MulBound(a, b, c, d)` above a product of two names gives `0 <= a * b <= c * d` from `0 <= a <= c` and `0 <= b <= d`, decision 0167. Dafny guesses on a product of two names, so write this line above each one. It is a proved lemma of the prelude, so it adds no axiom. An apply line can stand above the `return` of a pure member function. An assert line there has no rule yet.
- `std::unique_ptr<B>` of an interface works in the places of 0142, decision 0168. `std::make_unique<D>(a)` of a final class over `B` gives it, also at a call argument, and `p->f(a)` calls the virtual function in code and in a contract. Write `p != nullptr` in a requires line before you call through `p`. A move, a `std::unique_ptr<D>` held as itself, and a `std::unique_ptr<D>` from a call as a `std::unique_ptr<B>` have no rule yet.
- A pure virtual function that is not `const` writes its object, decision 0169. Its contract reads the const functions of the interface, with `old(f())` for the value before. A call runs through a parameter `B& b` on the modifies line, or through a local `std::unique_ptr<B>`, which takes the new value. `prove` checks each override on the contracts: its ensures lines must give those of the interface. A class at a `B&` parameter has no rule yet.
- A vector of `std::unique_ptr<B>` works as a `const&` parameter, a parameter by reference on the modifies line, or a local, decision 0170. A local `std::vector<T> v;` starts empty, and `v.push_back(std::make_unique<D>(a))` adds an element. `v[i]->f(a)` calls through the element, and a call that writes the object writes the element back. Its index must not read a value that the call writes. Write `v[i] != nullptr` in a requires line or an invariant above a line that reads `v[i]->f()`. A range-for over such a vector, an assignment to an element, and `std::move` of an element have no rule yet.
- `std::unique_ptr<B>` can be a field of a struct or a final class, and a parameter by value, decision 0171. Write `f_ != nullptr && f_->valid()` in a requires line above a line that reads `f_->g()`. Give it a value with `std::move(x)` of a local, or with `std::make_unique<D>(a)`. After `f(std::move(x));` or `T y = std::move(x);`, `x` is null. A statement that moves `x` must not read `x` again. A parameter can move in a return or a constructor init, as `f_(std::move(p))`. A move inside an `if` condition or an operator has no rule.
- A tree of `std::unique_ptr` nodes works, decision 0186. `std::make_unique<S>()` of a plain struct gives each field its initializer, which must be a constant expression. Write `n->f = e` through a local `std::unique_ptr<S>`, also with `e` as `std::move(x)`. A parameter by value can move anywhere a local moves, and it is null after the move. `return n;` of a local `std::unique_ptr` of a plain struct moves it. Dafny proves that `n` is not null at each write.
- A pure member function can hold locals before its `return`, if the body writes no local, decision 0172. It can call a `const` virtual function of an interface, also through a field, as in `return inner_ != nullptr && inner_->valid();`. Such a call can stand anywhere in code, also on the right of `&&`. A call of a member function of the same class, or of a pure member function of another struct, makes the body no pure body. An override with such a body gets no function, so the translator refuses its class.
- A free function that reads a global lists it on a `//@ reads` line, and one that changes it lists it on `//@ modifies`, decision 0173. A static data member has its full name, as in `//@ modifies Registry::last_id`. The translator makes each listed global a parameter, so a call can change only the globals that the callee lists. A function with a reads line cannot call one that changes the same global. A member function that lists a global, and a global that is no integer, `bool` or struct, have no rule yet.
- A static member function is a free function with its full name, decision 0174. One with a reads line, no modifies line and one `return` can be called in a contract, as `valid()` inside its class or `Tally::count()` anywhere. Put `valid()` first in a line that also calls a function that requires it. `return f();` works also when `f` changes a global. A static with no contract line has no rule yet.
- An `enum class` with a value written for an enumerator is its underlying integer, and `Flag::Read` is its value, decision 0175. `a & b` and `a | b` on unsigned integers prove with the laws of the bits. Write parentheses around a bit operator in a contract, because `==` binds tighter. A contract reads `static_cast<T>(e)` of a parameter, a field or `result` only when each value of `e` fits `T`. A free `operator+` is a function. `std::chrono::milliseconds` is its count, so a contract writes `a.count()`. A `std::array` by value or as a result is a sequence of its fixed length, and `return {a, b, c};` gives it. A `const int32_t&` parameter is the value.
- A contract can call a free function by its name, as `has(result, flag)`, decision 0176. Its body must be one `return` with no call, and it must write nothing. Such a function shows its body to every caller. One that no contract calls stays a wall: its callers prove from its contract alone. In code, put a call of it alone, in the start value of a local or in a `return`. Do not give a function of the file the name of a function of the companion file.
- `x++` and a call that writes a value back can stand inside an expression, decision 0177. Write one change of state in each expression, and do not read the changed name again in it. A `return` can call a function on the right of `&&` or `||` or in a branch of `?:`. A loop condition cannot hold a write or a call.
- A struct can have a destructor, decision 0178. Give the destructor a contract with `//@ modifies`, `//@ requires` and `//@ ensures` lines. The destructor runs where its local dies: before a `return`, and at the end of its block. Locals die in the reverse order of their declaration. Build such a local by its constructor, and use it only by its name and its member functions. Do not copy it, return it or keep it in a field. Do not pass it by value. Pass it by a reference that can change it. Do not keep it in a vector, an optional or a `unique_ptr`. Do not declare it in the head of a `for`. Do not call its destructor in code.
- A struct with a destructor can move, decision 0179. Write a move constructor `T(T&& other)` with `//@ modifies other`, and give the struct a destructor with a body and a contract. A destructor `= default` is no destructor here. Take a handle as `T&&` and list it on the `modifies` line. Write `T y = std::move(x);` or pass `std::move(x)` to a `T&&` parameter. Do not read `x` after the move. `x` still dies at the end of its block, so its destructor must release nothing after a move out of it. A constructor body can write globals and parameters, also a field of `other`. It cannot read or write a field of the new object or use `this`.
- A free function template with type parameters only proves at each type that the file uses it at, decision 0180. Each instance proves alone, so a contract can hold at `int64_t` and fail at `int32_t`. Put the contract lines above the line `template <...>`. Use the template in the file, or write an explicit instantiation. The translator refuses a template with no instance. Do not write a member function template or a template parameter that is not a type.
- A temporary of a plain struct, as `Pair{1, 2}`, can be the argument of a `const T&` parameter, decision 0181. It is its value. Do not return a temporary from a function that returns a reference, because the temporary dies at the end of the `return`.
- A function that returns a reference, a pointer or a span gives back only what its parameters by reference or `this` reach, decision 0182. A pointer or a span parameter counts as one by reference. The gate follows the `return` through each call. A local, a parameter by value, a structured binding by copy and a capture by copy die when the function returns.
- A member function that writes its object can return `T&` and end in `return *this;`, decision 0183. Then a chain `x.f(a).g(b)` runs each step in order on `x`. Write the chain as a statement, as the value of a `return` or as the start value of a local. Do not put it in a condition, an operand, an argument or the head of a `for`. Do not write `&result == this` in its contract.
- A local `std::array<T, N>` can start from a brace list of exactly `N` values, decision 0184. The code reads and writes its elements, and passes it to a sequence parameter. The translator refuses a shorter list and any other start value.
- A function can take `std::vector<T>&&` and list it on the `modifies` line, decision 0185. Pass `std::move(v)` to it. `std::vector<T> w = std::move(v);` gives `w` the value of `v`, and then `v` has any value. Do not read `v` after the move. A local `std::vector<T> v(n, x);` holds `n` copies of `x`.
- After a `push_back`, a read of `v.size()` in code needs a requires line or an invariant that bounds the length. Then the size fits `size_t`.
- An ensures line that reads `v[i]` after the call needs a line before it that gives the length: `ensures v.size() == old(v.size())`, or `+ 1` after one `push_back`, decision 0146. A loop that writes `v` needs the same line as an invariant.
- The gate also reads `modifies` and `reads` lines for globals, decision 0035.

The companion file:
- `NAME.spec.dfy` next to `NAME.cpp` holds the functions, predicates and lemmas that the contracts name, decisions 0079, 0080 and 0099.
- Each lemma has a body. A lemma or a function with no body is an axiom, and the translator refuses it.
- A count with `std::count_if` names a function here that counts with `CountIf` and the same test as the lambda, such as `CountIf(s, (x: int32) => x as int > k)`, decision 0149. A companion file cannot declare the name `CountIf`.
- A sequence parameter of a companion function or lemma is `seq<T>`, and an integer parameter is `int`. A multiset fact, such as "the same elements and x", is a predicate here, decision 0148. See `examples/sorted_insert`.
- A name must not start with a prefix of the model: `v_`, `c_`, `S_`, `E_`, `f_`, `b_` or `trunc_`, decision 0083.

Trusted code and calls:
- `CPLUSP_TRUSTED("reason")` above a function makes its contract an axiom. `prove` names each one on a `Trusted:` line, decisions 0102 and 0103.
- The gate bans a cast that changes the type a pointer or a reference points to, row `type_punning`, decision 0116. A cast to bytes stays allowed. The row also bans a raw copy that can make a bad value, decisions 0118 to 0120. A raw copy is a bit cast, `memcpy`, `memmove`, `memset` or a write through bytes that are not const. The row holds in trusted code too. Read the bits of a value with `std::bit_cast`.
- The gate cannot see three tricks in trusted code, decision 0120. Never write them. A human reviewer refuses each one.
  - A library function that writes bytes through a `void*` parameter into a type that is not bytes, for example `fread`, `read`, `recv` or `getrandom` into a `bool`. Read into a buffer of bytes, then check each value and convert it.
  - Two allowed copies in a row that move padding into a type that is not bytes. Copy each field by name.
  - Placement new of one type over an object of another type.
- A call inside an expression runs before its statement, when C++ runs it once, decision 0104.
- A call that writes back its object or a reference stands alone, or is the start value of a local, decisions 0096 and 0108.
## signed_overflow

Map `int32_t` to `newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000`, never to `int`.
Dafny then checks every arithmetic step for overflow, in the body and in the contract alike.
A sum that may overflow needs a precondition written with `as int`:
`requires -0x8000_0000 <= (a as int) + (b as int) < 0x8000_0000`.
The other mitigation is in the C++: add in `int64_t` and check the range before narrowing.

## unsigned_wrap

Map `uint32_t` to `newtype uint32 = x: int | 0 <= x < 0x1_0000_0000`.
Unsigned arithmetic wraps in C++ and does not wrap in Dafny.
Where the C++ means to wrap, write `wrap32((a as int) - (b as int))` with the helper `wrap32(x: int) = (x % 0x1_0000_0000) as uint32`.
Dafny `%` is never negative, so this is the C++ result.
Where the C++ does not mean to wrap, add a precondition such as `requires b <= a`.

## integral_promotion

C++ promotes types narrower than `int` to `int` before arithmetic.
Model the sum in `int32`: `(a as int32) + (b as int32)`.
Convert the result back with a wrap helper such as `wrap8(x: int) = (x % 0x100) as uint8`.
A conversion to an unsigned type wraps in C++, so the helper is exact.
For a signed target type, see `narrowing_cast`.

## signed_division

Dafny uses Euclidean division with a nonnegative remainder. C++ signed division truncates toward zero.
Never carry `/` or `%` over on signed values.
Use `trunc_div(a, b)` and `trunc_rem(a, b)`, which divide the absolute values and then set the sign.
The contract must require `b != 0`.
It must also exclude `a == INT32_MIN && b == -1`, because the quotient does not fit.

## narrowing_cast

Dafny `x as int8` needs a proof that `x` fits in `int8`.
The model never wraps, although C++20 does.
Put the fit in the C++ contract: `requires -0x80 <= x < 0x80`.
If the C++ means to wrap, it must wrap in its own code and then cast a value that fits.

## shift

Dafny has shifts on bit-vector types only, so map `uint32_t` to `bv32` in code that shifts.
Dafny accepts a shift by the full width, but C++ does not.
Write `requires n < 32`, never `requires n <= 32`.
The same holds for right shifts and for every other width.
The translator models `a >> n` as `shr(a, n, W)`, with `W` the width after promotion, decision 0106. Dafny proves `0 <= n < W` at each shift.
The translator has no rule for `<<` yet.

## sign_compare

Dafny will not compare an `int32` with a `uint64`, and `as int` on both sides gives the true comparison, not the C++ one.
C++ converts the signed operand to unsigned first, so a negative value compares as a huge value.
Do not model a mixed comparison as it stands.
Change the C++ to test the sign and cast on purpose, for example `i < 0 || static_cast<size_t>(i) < n`.
Model the changed C++ as `i < 0 || (i as uint64) < n`.
`std::cmp_less(i, n)` from `<utility>` is the same test, and its model is `(i as int) < (n as int)`.

## plain_int

Map only fixed-width types, such as `int32_t` to `int32` and `uint8_t` to `uint8`.
The compiler sets the width of plain `int`, `long`, `short` and `char`, and the source does not.
Do not guess a width for them.
Change the C++ to a fixed-width type, and then model that.
Map `size_t` to `uint64`, which assumes a 64-bit target.

## reference_aliasing

A non-const reference parameter is a value in and a value out of the model, decision 0029.
A value model cannot see two names for one object.
So the gate refuses a call in which two reference arguments reach one object and one of them can write, row `aliasing`, decision 0033.
No contract carries a clause about addresses. A value has no address.
A const reference is a value in.
Name each non-const reference parameter on the `//@ modifies` line, decision 0108. In an ensures line, `x` is the value after the call and `old(x)` the value before it.

## const_alias

A const reference is a value in, and a non-const reference is a value in and a value out.
A const reference to the object another argument writes is not a value in. The write changes it under the call.
So the gate refuses a call that passes one object to a non-const and to a const reference, row `aliasing`, decision 0033.
The same holds for a struct beside its member, a container beside itself, and an owner beside what it owns.
Pass two objects, or copy the value out first and pass the copy.

## evaluation_order

Dafny has no method call inside an expression, so the model must choose an order.
C++ orders the right side of an assignment before the left. It orders the operands of `&&`, `||`, the comma and `?:`, and a call's arguments before its body.
It does not order the arguments of one call among themselves, nor the operands of an arithmetic or comparison operator. Compilers differ there.
Never model two changes of state that C++ leaves unordered. The gate refuses them.
Beside one unordered change, only a literal or a local the change does not write may stand. The gate refuses a call, a global or a member of the written object there, decision 0033.
Where C++ orders them, hoist the calls into statements in that order, and model `&&`, `||` and `?:` as an `if`.

## loop_underflow

Dafny refuses `n - 1` on an unsigned value when `n` may be 0.
Do not model code that relies on a wrap below zero.
Change the C++ to count down to zero without going below it: `for (size_t i = n; i > 0; --i)`, and use `i - 1` inside.
A test `i >= 0` on an unsigned counter is always true, and the loop never ends.
Give every loop an invariant and a `decreases` clause.

## index_out_of_range

Model an array or a vector as a `seq`, and its size as a fact about `|a|`.
Every subscript becomes `a[i]`, and Dafny asks for a proof that the index is in range.
Do not weaken the proof. Write `requires i < |a|` in the contract, so the caller carries the obligation.

## optional_deref

Model `std::optional<T>` as `datatype Option<T> = None | Some(value: T)`.
Model `*opt` as `opt.value`. Dafny then asks for a proof that `opt` is `Some`.
Write `requires opt.Some?` in the model and `requires opt.has_value()` in the C++ contract.

## bool_from_int

Dafny has no conversion from an integer to `bool`.
Where C++ converts an integer to `bool`, write `x != 0` in the model.
Every value other than 0 is true, including values other than 1.

## promotion_before_widening

C++ does arithmetic in the type of the operands, not in the type of the destination.
`a * b` on two `int32_t` is an `int32_t` product, and overflow in it gives undefined behaviour, even when the result goes into an `int64_t`.
When the result stays in `int32_t`, model the product in `int32` with the contract that it fits.
When the result widens, the gate refuses `a * b`. Widen an operand in the C++, `int64_t{a} * b`, and model the product in `int64`.

## implicit_narrowing

Dafny refuses an implicit narrowing, and so does the gate.
Cast on purpose, and put the fit in the C++ contract: `requires -0x80000000 <= x < 0x80000000`.
The model is then `x as int32`.
See `narrowing_cast`.

## compound_assign_narrow

A compound assignment on a type narrower than `int` computes in `int` and narrows on the store.
Write the narrowing as a cast: `a = static_cast<uint8_t>(a + 100)`.
Model it with the wrap helper: `wrap8(((a as int32) + 100) as int)`.

## signed_to_unsigned

The model refuses a signed value where the code needs an unsigned one, and so does the gate.
Put the sign in the contract, `requires i >= 0`, and cast on purpose.
The model is then `i as uint64`.

## unary_minus_min

`-x` has one value that does not fit.
The contract must exclude it: `requires x != -0x8000_0000`.

## abs_min

Model `std::abs` as `if x < 0 then -x else x`.
Exclude `INT32_MIN` in the contract: `requires x != -0x8000_0000`.

## increment_overflow

`++` and `--` are arithmetic.
They need the same contract as `+ 1` and `- 1`.
For `++x` write `requires x < 0x7FFF_FFFF`.

## signed_shift_left

Model a signed shift through `bv32`.
Convert a negative value by adding 2^32 first, and convert back by subtracting 2^32 when the top bit is 1.
State the postcondition on the bit pattern, `to_bv32(result) == to_bv32(x) << n`. Dafny proves the concrete values from it, not the general congruence.

## signed_shift_right

Dafny `/` rounds toward negative infinity when the divisor is positive, and `2^n` is positive.
Model a right shift as a division by a power of two.
Dafny `/` matches the C++ shift here. It never matches C++ `/` on negative values, see `signed_division`.

## literal_shift

A literal has its own type, and a shift takes the type of its left operand.
`1 << n` is a shift in `int`, whatever the type of the destination.
Write the literal in the destination type: `int64_t{1} << n`.

## bool_arith

C++ promotes `bool` to `int` in arithmetic.
Dafny does not.
Write `if b then 1 else 0`.

## enum_cast

Model an `enum class` as a datatype of its enumerators.
The gate bans each cast to an `enum class` whose enumerators have no values written, also in trusted code, row `enum_cast`, decision 0114. To make one from a number, switch on the number and return an enumerator for each case.
A flags type, where `|` makes values no enumerator names, is a `bv32` in the model, and a cast to it needs no enumerator precondition.
The translator takes an `enum class` whose enumerators have no values written, decision 0109. It refuses a cast of an enum and every operator except `==` and `!=`, in code and in contracts.
A `switch` over such an enum is a match. The translator refuses a `default`, a `[[fallthrough]]`, several labels on one body, and a `break` that does not end a case.

## size_minus_one

`size()` returns an unsigned value.
`size() - 1` on an empty container is the largest `size_t`, and it is no error.
The contract must require a non-empty container, or the C++ must test `empty()` first.

## value_semantics

A C++ value is a Dafny `datatype`.
Model a struct or class held by value as a datatype, and a copy as the same value.
A field update is `p.(x := 5)`, a new value.
Never a Dafny `class`. What the C++ reaches through a reference is the value in and the value out, decision 0029.

## object_lifetime

Dafny objects live for ever, and C++ objects die.
A pointer in verified code is a parameter only, never a member or a local.
So it cannot be stored past its object.

## reference_into_container

A `seq` element is a value, and a C++ reference into a container dies at the next mutation.
Copy the element out.
Never hold a reference into a container.

## member_init_order

C++ initializes members in declaration order, whatever order the constructor writes them in.
Write the mem-initializers in declaration order, and model the constructor in that order.

## slicing

A datatype value keeps its constructor, and a C++ copy into a base type loses the derived part.
Never copy a derived object into a base by value.
Pass it as a reference parameter.

## virtual_in_constructor

A virtual call inside a constructor or destructor dispatches to the class under construction.
In the model a constructor builds a value, and a call on it is a call on the finished value.
Do not call a virtual function from a constructor or destructor.

## virtual_destructor

Dafny has no destructor, so the model cannot see a wrong one.
Every class with a virtual function has a virtual destructor.
The gate enforces it.

## use_after_move

A moved-from value is unspecified, and Dafny has no move.
Never read a variable after `std::move` of it.
Model the move as a copy and the source as gone.

## moved_from_unique_ptr

A moved-from `unique_ptr` is null.
Model `unique_ptr<T>` as an `Option<T>` value, and a move as the source becoming `None`.
Never read the source after the move.

## null_pointer

Model a pointer parameter as an `Option<T>` value.
Dafny then asks for `p.Some?` at every read.
Put it in the contract.

## operator_meaning

An overloaded operator is a function.
Model `a + b` on a class type as a call to that function with its own contract, never as the built-in operator.

## generic_per_type

A template has no model.
Each instantiation is a function with its own types, and gets its own model.
The gate reads inside instantiations too.

## stack_depth

Dafny proves that a recursion ends, not that the stack holds it.
Bound the depth in the contract.
The bound is an assumption about the target, and docs/soundness.md gap 1 records it.

## radix_find

A node that holds a std::vector of nodes is one recursive datatype with a seq of children.
A find in a tree proves what the tree stores, with Wellformed for the shape it relies on.

## constexpr_runtime

`constexpr` changes nothing in the model.
The compiler checks only the calls it evaluates at compile time.
A run-time call has the same contract as any function.

## interface_dispatch

A pure interface is an opaque type with its contract as the only functions known about it.
A class that implements several interfaces meets each contract on its own type.
The upcast is an axiom that says only `f(As(x)) == f_impl(x)`. A lemma proves `f_impl` meets the interface contract, or the two axioms can contradict and prove anything.
Dispatch through any of them is a call on the same value.

## array_index

Model `std::array<T, N>` as a `seq<T>` with `|a| == N`.
Every subscript needs `requires i < N` in the contract, as for a plain array.

## span_dangling

A span is a pointer and a length, and Dafny has only values.
A span is a parameter only, never stored.
The gate enforces it.

## range_for_mutation

A Dafny loop over a `seq` reads a value.
A C++ range-for holds iterators into the live container.
The loop body never changes the range.
The gate refuses a direct call on the range, and a call that passes the range by non-const reference.

## count_if_lambda

A lambda passed to a std algorithm with by-value captures and no `mutable` is a pure function of its arguments and its captures.
Model the algorithm and the lambda together as one function over the `seq`.
`std::count_if(v.begin(), v.end(), [captures](T x) { return e; })` over a sequence parameter is `CountIf(v, (x: T) => e)` of the prelude, as an `int64`, decision 0149.
The lambda has one parameter of the element type, by value or by `const&`, and its body is one `return` with no call.
Each count needs a requires line or an invariant that keeps `v.size()` below 2^63. Without it, the fit of the `int64` fails.
The translator refuses any other algorithm, any other range, and an init capture.

## fold_init_type

A fold runs in the type of its init value.
Write the init value in the element type, or a wider one.
The gate enforces it.

## sort_contract

Model a std algorithm with a trusted contract as a bodyless `{:axiom}` method with that contract, and call it from the model of your function.
Never mark the model of your own function `{:axiom}`.
The trusted algorithms so far are `std::sort`, an axiom method with its contract in this skill, and `std::count_if`, modelled as a function over the `seq`.
`std::sort` gives a sorted permutation.
The comparator must be a strict weak order, and the default one on integers is.

## map_subscript

`m[k]` on a map writes.
Never model it as a read.
Use `contains` and `at`, which the gate allows, and model them as `k in m` and `m[k]`.

## string_npos

`std::string::find` returns `npos` for no match, and arithmetic on it wraps.
Text in verified code is a span of bytes, decision 0031. The gate refuses `std::string` and `std::string_view`.
A search returns `std::optional<size_t>`, and the model of it is `Option<nat>`.
Never do arithmetic on a position before the `None` case is handled.

## switch_fallthrough

A `switch` falls through to the next case without a break, and a Dafny `match` never does.
No case runs into the next without `[[fallthrough]]`, and the gate enforces it.
In a hand-written model, a marked fall-through is one arm with both bodies. The translator refuses it, decision 0109.

## switch_missing_case

A Dafny `match` must cover every value, and a C++ `switch` need not.
Write a case for every enumerator, or a default.
The gate enforces it.

## optional_compare

A comparison of an optional with a value has a result when the optional is empty.
An empty optional is less than every value and equal to none.
Write the empty case out: `o.None? ||` for `<`, `<=` and `!=`, and `o.Some? &&` for `==`, `>` and `>=`.

## variant_get

Model `std::variant` as a datatype with one constructor per alternative.
A read of an alternative needs `requires` that the variant holds it, in the C++ contract and in the model.

## double_sum

A double is a real after rounding.
Model `a + b` as `fadd(a, b)`, and state the result as a bound, `abs(result - (a + b)) <= EPS * abs(a + b) + ETA`.
Never state equality of two double results.
The bound holds up to `MAX`, so require `abs(a) <= MAX / 4.0` and `abs(b) <= MAX / 4.0`.
Each operation carries the bound of its one rounding, so `fadd(a, b)` gives the bound with no call of `RoundError`, decision 0153.
In the C++ contract, write the bound as `|result - (a + b)| <= eps * |a + b| + eta`, with `eps` as `DBL_EPSILON / 2` and `eta` as `DBL_TRUE_MIN / 2`, and the magnitude bound `|a| <= DBL_MAX / 4` as a `requires`.
The model is `divergence/dafny/Double.dfy`. Write `include "Double.dfy"` with the path to it, and `import opened Double`.

## double_nan

The model has no NaN and no infinity.
Every `double` parameter requires `std::isfinite` in the C++ contract.
Never compare doubles with `==`. The gate refuses it.
Compare against a tolerance `T` that is a double, and give the contract slack for the rounding of the difference.
`result` implies `|a - b| <= T + 2 * eps * T + 2 * eta`, and `|a - b| <= T - 2 * eps * T - 2 * eta` implies `result`.
Model the difference as `fsub(a, b)`, never as the exact difference.

## double_to_int

Model `static_cast<int32_t>(x)` as truncation toward zero, not `Floor`.
Write `trunc(x)` as `if x >= 0.0 then x.Floor else -((-x).Floor)`.
The contract requires the value to fit: `requires -2147483649.0 < x < 2147483648.0`.

## double_cancellation

Every operation rounds, and the errors add.
State the bound from the magnitudes of the operands, not from the result the mathematics would give.
Each operation rounds once, and `fadd` to `fdiv` each carry the bound of that one rounding, decision 0153.
Each rounding adds `eta`, so a chain of roundings carries a small multiple of `eta` in its bound.

## double_increment

A bound of `EPS * abs(x)` is 1.0 at 2^53, so above it the model promises nothing about the last digit.
When the C++ needs exact counting, use an integer type.

## double_division_zero

The model has no infinity, and C++ calls division of a double by zero undefined.
The contract requires a non-zero divisor: `requires b != 0.0`.
The quotient must stay below `MAX`, so the model needs `requires abs(a / b) <= MAX`, and the C++ contract carries `|a / b| <= DBL_MAX`.

## int_to_double

An integer converts to a double exactly up to 2^53 in magnitude.
The contract requires that range, and `RoundExactInt` proves the equality.
Model the conversion as `round(n as real)`.

## pointer_into_container

A pointer parameter and a container cannot alias in the model, and in C++ a pointer into the container dies at the next mutation.
Never take the address of a container element.
The gate refuses it.

## double_underflow

A product or quotient can fall below the smallest subnormal and round to 0.
The `eta` term of the bound is what allows it.
State `|a * b| <= DBL_MAX` in the C++ contract, and never a lower bound.

## single_precision

The model is of `double` and of no other type.
Never write `float` or `long double` in verified code. The gate refuses them.
A `float` from outside is converted to `double` in trusted code at the edge, and the contract there is about the `double`.


## double_literal

A literal in the C++ is the nearest double, not the real it spells. The model reads the real.
Write only literals that are exactly a double: a hex float, or a decimal such as 0.5, 1e3 or the exact expansion of a double. The gate refuses the others.
For a tenth, divide by `10.0` instead of multiplying by `0.1`.

## unlisted_modifies

A global is a field of the State value.
Every function that changes it takes the State in and gives it back. In the C++ contract that is `modifies total`.
A trusted contract that omits it is false.
The gate reads the `modifies` and `reads` lines, decision 0035, and refuses an access to a global they do not list, also through a call.
It judges the code the compiler generates, decision 0037, so a destructor, a copy or a lambda inside a std call counts where it runs.
The gate reads the lines of a trusted function too, so a trusted body that forgets one is refused. A reviewer still reads what the lines claim.
A name on the line that names a reference parameter is that parameter, not a global with the same name, decisions 0111 and 0112.

## static_local

A function-local static is a global with a name no caller's contract can list. The gate refuses it.
Use a static data member or a global, and list it in `modifies` or `reads`.
Model it as a field of the State value that the function takes in and gives back.
Never model it as a local.

## global_constructors

A global with a dynamic initializer runs in an order the standard leaves open across files.
Model no such global.
Compute the value in a function, or make it `constexpr` or `constinit`.
The gate enforces it.

## torn_read

A variable another thread may change has no value, only a fresh read each time.
Model its getter as a method that does not constrain its result between calls.
The contract of the getter says only what every writer keeps, for example a range.
The getter is trusted code, and it must read an atomic. A plain read of a variable another thread writes is a data race.
Never prove two reads equal.

## untyped_literal

A literal with no typed operand is an exact integer in Dafny.
`2147483647 + 1 > 0` is true in Dafny, and in C++ the sum overflows.
Give each literal its type, such as `(1 as int32)`.
Then Dafny checks each step, and code that overflows does not prove.

## seq_length

A Dafny `seq` has no bound on its length, and a C++ sequence has at most `SIZE_MAX` elements.
To read `|v|` as a `uint64`, give each sequence the type `Vec<T>`, a `seq<T>` with `|s| < 0x1_0000_0000_0000_0000`.
Every C++ sequence meets that, and the bound also holds for a sequence inside a struct.

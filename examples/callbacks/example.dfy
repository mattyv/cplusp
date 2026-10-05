// A function template has no model. Each functor type it is used at gets its own datatype and its own method, decision 0029. A functor
// is a datatype of its fields, and a const operator() is a function over it. Halve has no field. CapAt has a limit. The method for
// each instantiation has the contract of the template, with f(f(x)) written as two calls of the function for that type. Dafny `/` rounds
// toward negative infinity and C++ rounds toward zero, so the division is trunc_div.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function iabs(x: int): int {
  if x < 0 then -x else x
}

function trunc_div(a: int, b: int): int
  requires b != 0
{
  var q := iabs(a) / iabs(b);
  if (a < 0) != (b < 0) then -q else q
}

datatype Halve = Halve

function call_Halve(f: Halve, x: int32): int32
  ensures call_Halve(f, x) as int == trunc_div(x as int, 2)
{
  trunc_div(x as int, 2) as int32
}

datatype CapAt = CapAt(limit: int32)

function call_CapAt(f: CapAt, x: int32): int32
  ensures call_CapAt(f, x) == (if x < f.limit then x else f.limit)
{
  if x < f.limit then x else f.limit
}

method apply_twice_Halve(f: Halve, x: int32) returns (result: int32)
  ensures result == call_Halve(f, call_Halve(f, x))
{
  result := call_Halve(f, call_Halve(f, x));
}

method apply_twice_CapAt(f: CapAt, x: int32) returns (result: int32)
  ensures result == call_CapAt(f, call_CapAt(f, x))
{
  result := call_CapAt(f, call_CapAt(f, x));
}

method quarter(x: int32) returns (result: int32)
  ensures result as int == trunc_div(x as int, 4)
{
  result := apply_twice_Halve(Halve, x);
}

method cap_twice(x: int32, limit: int32) returns (result: int32)
  ensures result == (if x < limit then x else limit)
{
  result := apply_twice_CapAt(CapAt(limit), x);
}

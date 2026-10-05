// Dafny `/` rounds toward negative infinity, and C++ rounds toward zero, so the model divides with trunc_div.
// The contract excludes the one quotient that does not fit, and the unsigned subtraction needs b <= a, as it does in C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

function abs(x: int): int {
  if x < 0 then -x else x
}

function trunc_div(a: int, b: int): int
  requires b != 0
{
  var q := abs(a) / abs(b);
  if (a < 0) != (b < 0) then -q else q
}

method quotient(a: int32, b: int32) returns (result: int32)
  requires b != 0
  requires !(a == -0x8000_0000 && b == -1)
  ensures result as int == trunc_div(a as int, b as int)
{
  result := trunc_div(a as int, b as int) as int32;
}

method distance(a: uint32, b: uint32) returns (result: uint32)
  requires b <= a
  ensures result as int == a as int - b as int
{
  result := a - b;
}

// A shift needs bit-vectors, so this method uses bv32. Dafny accepts a shift by the full width and C++ does not,
// so the count stops one short of it.
method shift_right(x: bv32, n: bv32) returns (result: bv32)
  requires n < 32
  ensures result <= x
  ensures n == 0 ==> result == x
{
  result := x >> n;
}

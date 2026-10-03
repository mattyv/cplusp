// Model B: truncating helpers, so the model rounds toward zero as C++ does.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function abs(x: int): int {
  if x < 0 then -x else x
}

function trunc_div(a: int, b: int): int
  requires b != 0
{
  var q := abs(a) / abs(b);
  if (a < 0) != (b < 0) then -q else q
}

function trunc_rem(a: int, b: int): int
  requires b != 0
{
  var r := abs(a) % abs(b);
  if a < 0 then -r else r
}

// The C++ rule: (a / b) * b + a % b == a.
lemma DivisionIdentity(a: int, b: int)
  requires b != 0
  ensures b * trunc_div(a, b) + trunc_rem(a, b) == a
{
}

lemma TruncatesTowardZero()
  ensures trunc_div(-7, 2) == -3 && trunc_rem(-7, 2) == -1
  ensures trunc_div(7, -2) == -3 && trunc_rem(7, -2) == 1
{
}

method quot(a: int32, b: int32) returns (result: int32)
  requires b != 0
  requires !(a == -0x8000_0000 && b == -1)
  ensures result as int == trunc_div(a as int, b as int)
{
  result := trunc_div(a as int, b as int) as int32;
}

method rem(a: int32, b: int32) returns (result: int32)
  requires b != 0
  requires !(a == -0x8000_0000 && b == -1)
  ensures result as int == trunc_rem(a as int, b as int)
{
  result := trunc_rem(a as int, b as int) as int32;
}

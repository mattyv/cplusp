// Dafny has no call inside an expression, so the model chooses an order, and the C++ has one call per statement to match it.
// The && is modelled as an if: the second call runs only when the first result is positive, as in C++.
// A reference parameter is a value in and a value out, decision 0029. The clause `requires &x != &y` is a fact about the two
// C++ names and has no counterpart on values. The caller proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method next(x: int32) returns (x': int32, result: int32)
  requires x < 0x7FFF_FFFF
  ensures x' == x + 1
  ensures result == x
{
  result := x;
  x' := x + 1;
}

method two_steps(x: int32) returns (x': int32, result: int32)
  requires 0 <= x < 0x3FFF_FFFF
  ensures x' == x + 2
  ensures result as int == 2 * (x as int) + 1
{
  var x1, first := next(x);
  var x2, second := next(x1);
  x' := x2;
  result := first + second;
}

method both_positive(x: int32, y: int32) returns (x': int32, y': int32, result: bool)
  requires x < 0x7FFF_FFFF && y < 0x7FFF_FFFF
  ensures x' == x + 1
  ensures y' == (if x > 0 then y + 1 else y)
  ensures result == (x > 0 && y > 0)
{
  var x1, a := next(x);
  x' := x1;
  if a > 0 {
    var y1, b := next(y);
    y' := y1;
    result := b > 0;
  } else {
    y' := y;
    result := false;
  }
}

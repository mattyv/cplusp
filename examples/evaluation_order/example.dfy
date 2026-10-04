// Dafny has no call inside an expression, so the model chooses an order, and the C++ has one call per statement to match it.
// The && is modelled as an if: the second call runs only when the first result is positive, as in C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method next(x: Ref) returns (result: int32)
  requires x.v < 0x7FFF_FFFF
  modifies x
  ensures x.v == old(x.v) + 1
  ensures result == old(x.v)
{
  result := x.v;
  x.v := x.v + 1;
}

method two_steps(x: Ref) returns (result: int32)
  requires 0 <= x.v < 0x3FFF_FFFF
  modifies x
  ensures x.v == old(x.v) + 2
  ensures result as int == 2 * (old(x.v) as int) + 1
{
  var first := next(x);
  var second := next(x);
  result := first + second;
}

method both_positive(x: Ref, y: Ref) returns (result: bool)
  requires x != y
  requires x.v < 0x7FFF_FFFF && y.v < 0x7FFF_FFFF
  modifies x, y
  ensures x.v == old(x.v) + 1
  ensures y.v == (if old(x.v) > 0 then old(y.v) + 1 else old(y.v))
  ensures result == (old(x.v) > 0 && old(y.v) > 0)
{
  var a := next(x);
  if a > 0 {
    var b := next(y);
    result := b > 0;
  } else {
    result := false;
  }
}

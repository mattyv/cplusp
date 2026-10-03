// Model B: the C++ now names each result in its own statement. The order in the model is the order in the C++.
// The Dafny is the same as the naive model. What changed is that the C++ promises the order.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method next(x: Ref) returns (result: int32)
  requires x.v < 0x7FFF_FFFF
  modifies x
  ensures x.v as int == old(x.v) as int + 1
  ensures result == old(x.v)
{
  result := x.v;
  x.v := x.v + 1;
}

function before(a: int32, b: int32): bool {
  a < b
}

method rises(x: Ref) returns (result: bool)
  requires x.v < 0x7FFF_FFFE
  modifies x
  ensures x.v as int == old(x.v) as int + 2
  ensures result == true
{
  var first := next(x);
  var second := next(x);
  result := before(first, second);
}

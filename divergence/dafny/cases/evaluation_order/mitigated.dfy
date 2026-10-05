// Model B: the C++ now names each result in its own statement. The order in the model is the order in the C++.
// A reference parameter is a value in and a value out, decision 0029. The model is the same as the naive one in its order.
// What changed is that the C++ promises the order.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method next(x: int32) returns (x': int32, result: int32)
  requires x < 0x7FFF_FFFF
  ensures x' as int == x as int + 1
  ensures result == x
{
  result := x;
  x' := x + 1;
}

function before(a: int32, b: int32): bool {
  a < b
}

method rises(x: int32) returns (x': int32, result: bool)
  requires x < 0x7FFF_FFFE
  ensures x' as int == x as int + 2
  ensures result == true
{
  var x1, first := next(x);
  var x2, second := next(x1);
  x' := x2;
  result := before(first, second);
}

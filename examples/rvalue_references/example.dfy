// A move is a copy, and the source is gone. After the call the model gives v an unspecified value. A read of it would
// prove nothing, and the C++ does not read it. The callee owns its own value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method consume(v: seq<int32>) returns (result: uint64)
  requires |v| < 0x1_0000_0000_0000_0000
  ensures result as int == |v|
{
  result := |v| as uint64;
}

method build_and_consume() returns (result: uint64)
  ensures result == 3
{
  var v: seq<int32> := [0, 0, 0];
  result := consume(v);
  v :| true;
}

// A move is a copy, and the source is gone. After the move the model gives the source an unspecified value. A read of it would
// prove nothing, and the C++ does not read it. The statement after the havoc reads the new owner only.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method consume(v0: seq<int32>) returns (result: uint64)
  requires |v0| <= 0x7FFF_FFFF_FFFF_FFFF
  ensures result as int == |v0|
{
  var v := v0;
  var owned := v;
  v :| true;
  result := |owned| as uint64;
}

method build_and_consume() returns (result: uint64)
  ensures result == 3
{
  var v: seq<int32> := [0, 0, 0];
  var moved := v;
  v :| true;
  result := consume(moved);
}

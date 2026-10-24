// A vector by rvalue reference is a reference parameter, so consume gives back v'. A move gives the owner the value, and the source
// then has any value, decision 0185. The caller gets v back from the call and never reads it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method consume(v: seq<int32>) returns (result: uint64, v': seq<int32>)
  requires |v| <= 0x7FFF_FFFF_FFFF_FFFF
  ensures result as int == |v|
{
  v' := v;
  var owned := v';
  v' :| true;
  result := |owned| as uint64;
}

method build_and_consume() returns (result: uint64)
  ensures result == 3
{
  var v: seq<int32> := seq(3, _ => 0 as int32);
  result, v := consume(v);
}

// A reference is an object. The trusted read is a method with no body, an axiom with the contract of
// trusted.cpp. It has no modifies clause, so it leaves the object unchanged. The second read gives the same value as the first.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method {:axiom} read_through(x: Ref) returns (result: int32)
  ensures result == x.v

method doubled(x: Ref) returns (result: int32)
  requires -0x4000_0000 <= x.v < 0x4000_0000
  ensures result as int == 2 * (x.v as int)
{
  var a := read_through(x);
  var b := read_through(x);
  result := a + b;
}

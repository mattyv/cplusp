// A pointer parameter is a nullable reference. The trusted read is a method with no body, an axiom with the contract of
// trusted.cpp. It has no modifies clause, so the object is the same after it, and the second read gives the same value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method {:axiom} read_back(p: Cell?) returns (result: int32)
  requires p != null
  ensures result == p.v

method read_twice(p: Cell?) returns (result: int32)
  requires p != null
  requires -0x4000_0000 <= p.v < 0x4000_0000
  ensures result as int == 2 * (p.v as int)
{
  var a := read_back(p);
  var b := read_back(p);
  result := a + b;
}

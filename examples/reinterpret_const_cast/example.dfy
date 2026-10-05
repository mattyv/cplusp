// A const reference is a value in, decision 0029. The trusted read is a method with no body, an axiom with the contract of
// trusted.cpp. It returns no value for x, so the argument is unchanged after it. The second read gives the same value as the first.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} read_through(x: int32) returns (result: int32)
  ensures result == x

method doubled(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)
{
  var a := read_through(x);
  var b := read_through(x);
  result := a + b;
}

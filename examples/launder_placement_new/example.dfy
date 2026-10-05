// A pointer parameter is an Option value, decision 0029. The trusted read is a method with no body, an axiom with the contract of
// trusted.cpp. It takes the pointer and returns the value and no State, so the object is the same after it, and the second read
// gives the same value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method {:axiom} read_back(p: Option<int32>) returns (result: int32)
  requires p.Some?
  ensures result == p.value

method read_twice(p: Option<int32>) returns (result: int32)
  requires p.Some?
  requires -0x4000_0000 <= p.value < 0x4000_0000
  ensures result as int == 2 * (p.value as int)
{
  var a := read_back(p);
  var b := read_back(p);
  result := a + b;
}

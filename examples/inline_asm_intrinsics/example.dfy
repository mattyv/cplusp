// The trusted function is a method with no body, an axiom that states its contract. The intrinsic does not appear in the model.
// The caller calls it twice, and the second call needs its precondition proved from the first result.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} add_lanes(a: int32, b: int32) returns (result: int32)
  requires -0x4000_0000 <= a < 0x4000_0000
  requires -0x4000_0000 <= b < 0x4000_0000
  ensures result as int == a as int + b as int

method sum3(a: int32, b: int32, c: int32) returns (result: int32)
  requires -0x2000_0000 <= a < 0x2000_0000
  requires -0x2000_0000 <= b < 0x2000_0000
  requires -0x4000_0000 <= c < 0x4000_0000
  ensures result as int == a as int + b as int + c as int
{
  var ab := add_lanes(a, b);
  result := add_lanes(ab, c);
}

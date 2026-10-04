// The trusted function is a method with no body, an axiom that states its contract. The pointer does not appear in the model,
// since the contract says what the target does. The caller calls it twice, and the second call needs its precondition proved.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} increment(x: int32) returns (result: int32)
  requires x < 0x7FFF_FFFF
  ensures result as int == x as int + 1

method add_two(x: int32) returns (result: int32)
  requires x < 0x7FFF_FFFE
  ensures result as int == x as int + 2
{
  var y := increment(x);
  result := increment(y);
}

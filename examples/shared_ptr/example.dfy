// The trusted function is a method with no body, an axiom that states its contract. It speaks of the value, so the model has
// no reference count. The caller adds one, and Dafny checks that the sum fits from the bound in the contract.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} shared_value(x: int32) returns (result: int32)
  ensures result == x

method next_value(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == x as int + 1
{
  var v := shared_value(x);
  result := v + 1;
}

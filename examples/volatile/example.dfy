// The accessor is a method with no body, an axiom that states the range. It is a method and not a function, so two calls may
// return two values. The caller reads once, and proves the subtraction in range from the contract.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

method {:axiom} read_status() returns (result: uint32)
  ensures result <= 255

method headroom() returns (result: uint32)
  ensures result <= 255
{
  var s := read_status();
  result := 255 - s;
}

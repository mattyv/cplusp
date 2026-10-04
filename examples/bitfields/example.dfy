// The trusted function is a method with no body, an axiom that states its contract in plain integers. The caller adds one,
// and Dafny proves from the contract that the sum stays below 2^32.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

method {:axiom} low_bits(w: uint32) returns (result: uint32)
  ensures result as int == w as int % 8

method low_bits_plus_one(w: uint32) returns (result: uint32)
  ensures result as int == w as int % 8 + 1
{
  var low := low_bits(w);
  result := low + 1;
}

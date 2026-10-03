// Model C: bounded int32, and the contract says what the caller must guarantee.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method add(a: int32, b: int32) returns (result: int32)
  requires -0x8000_0000 <= (a as int) + (b as int) < 0x8000_0000
  ensures result as int == (a as int) + (b as int)
{
  result := a + b;
}

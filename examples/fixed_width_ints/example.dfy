// int32_t is a bounded type. The contract keeps a + b inside it, and Dafny checks the bound on the sum.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method add(a: int32, b: int32) returns (result: int32)
  requires -0x4000_0000 <= a < 0x4000_0000
  requires -0x4000_0000 <= b < 0x4000_0000
  ensures result as int == a as int + b as int
{
  result := a + b;
}

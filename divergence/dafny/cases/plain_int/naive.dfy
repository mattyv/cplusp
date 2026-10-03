// Model A: `int` is modelled as int32. Nothing in the C++ says int has 32 bits.
// The standard promises 16. The proof is for targets where it is 32, and the file does not say so.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method twice(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)
{
  result := 2 * x;
}

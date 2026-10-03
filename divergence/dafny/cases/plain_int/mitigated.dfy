// Model B: the C++ now says int32_t, which has exactly 32 bits. The model is exact on every target.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method twice(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)
{
  result := 2 * x;
}

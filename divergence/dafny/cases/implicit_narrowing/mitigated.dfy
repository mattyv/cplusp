// Model B: the C++ casts on purpose, and its contract says the value fits. Dafny keeps `as`.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method low(x: int64) returns (result: int32)
  requires -0x8000_0000 <= x < 0x8000_0000
  ensures result as int == x as int
{
  result := x as int32;
}

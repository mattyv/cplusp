// Model B: the C++ tests the sign first, then casts. Dafny checks the cast, so the sign test is not optional.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method below(i: int32, n: uint64) returns (result: bool)
  ensures result == ((i as int) < (n as int))
{
  result := i < 0 || (i as uint64) < n;
}

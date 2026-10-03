// Model B: the C++ states the sign in its contract and casts on purpose. Dafny checks the cast.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method index_of(i: int32) returns (result: uint64)
  requires i >= 0
  ensures result as int == i as int
{
  result := i as uint64;
}

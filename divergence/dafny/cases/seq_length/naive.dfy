// Model A: the vector as a seq with no bound. A seq can be longer than any size_t, so the cast of its length may not fit.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method count(v: seq<int32>) returns (result: uint64)
  ensures result as int == |v|
{
  result := |v| as uint64;
}

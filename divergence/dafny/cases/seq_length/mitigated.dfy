// Model B: each sequence is a Vec, a seq whose type bounds its length by what size_t holds. Every C++ sequence meets the bound,
// and the bound also holds for a sequence inside a struct, decision 0076.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000
type Vec<T> = s: seq<T> | |s| < 0x1_0000_0000_0000_0000 witness []

method count(v: Vec<int32>) returns (result: uint64)
  ensures result as int == |v|
{
  result := |v| as uint64;
}

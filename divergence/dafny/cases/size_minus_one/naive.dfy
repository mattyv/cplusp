// Model A: a vector as a `seq`, and `v.size() - 1` as `|v| - 1` on uint64.
// A vector size is a size_t, so the model says it fits in uint64. The subtraction is a range error for |v| == 0.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method last_index(v: seq<int32>) returns (result: uint64)
  requires |v| < 0x1_0000_0000_0000_0000
  ensures result as int == |v| - 1
{
  result := |v| as uint64 - 1;
}

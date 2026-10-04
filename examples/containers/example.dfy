// A vector of int32_t is a seq<int32>. The index bound is in the contract, so the subscript is in range.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method element(v: seq<int32>, i: uint64) returns (result: int32)
  requires i as int < |v|
  ensures result == v[i]
{
  result := v[i];
}

// Model B: the contract says the vector is not empty. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method last_index(v: seq<int32>) returns (result: uint64)
  requires |v| < 0x1_0000_0000_0000_0000
  requires |v| > 0
  ensures result as int == |v| - 1
{
  result := |v| as uint64 - 1;
}

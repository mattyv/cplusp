// Model B: the contract says the index is in range. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method at(a: seq<int32>, i: uint64) returns (result: int32)
  requires |a| == 4
  requires i < 4
  ensures result == a[i]
{
  result := a[i];
}

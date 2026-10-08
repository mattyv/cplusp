// Model B: each sequence parameter requires a length that fits size_t, which holds for every C++ sequence.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method count(v: seq<int32>) returns (result: uint64)
  requires |v| <= 0xFFFF_FFFF_FFFF_FFFF
  ensures result as int == |v|
{
  result := |v| as uint64;
}

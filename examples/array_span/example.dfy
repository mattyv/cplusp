// A span is a seq, and so is a std::array<int32_t, 4>, with the size as a fact about |a|. Every subscript needs a proof
// that the index is in range, and the contract carries it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method first(s: seq<int32>) returns (result: int32)
  requires |s| > 0
  ensures result == s[0]
{
  result := s[0];
}

method pick(a: seq<int32>, i: uint64) returns (result: int32)
  requires |a| == 4
  requires i < 4
  ensures result == a[i]
{
  result := a[i];
}

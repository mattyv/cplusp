// Model A: a std::array of four int32_t as a sequence of length 4, and the index carried over.
// Dafny asks for a proof that i is in range. There is none, so the model is stricter than C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method at(a: seq<int32>, i: uint64) returns (result: int32)
  requires |a| == 4
  ensures result == a[i]
{
  result := a[i];
}

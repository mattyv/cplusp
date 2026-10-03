// Model A: the map is a Dafny map, and `m[k]` is a read.
// Dafny asks for a proof that k is in m. There is none, so the model is stricter than C++.
// The C++ does not read. It inserts a value-initialized element when k is missing, and the map grows.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method value_or_zero(m0: map<int32, int32>, k: int32) returns (result: int32, m: map<int32, int32>)
  ensures result == (if k in m0 then m0[k] else 0)
  ensures |m| == |m0|
{
  m := m0;
  result := m[k];
}

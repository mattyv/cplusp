// Model B: the C++ uses `contains` and `at`, which model as `k in m` and `m[k]`. Neither changes the map.
// The model has the map before and after the call, and the postcondition says the two have the same size.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method value_or_zero(m0: map<int32, int32>, k: int32) returns (result: int32, m: map<int32, int32>)
  ensures result == (if k in m0 then m0[k] else 0)
  ensures |m| == |m0|
{
  m := m0;
  result := if k in m then m[k] else 0;
}

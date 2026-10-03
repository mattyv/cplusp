// Model B: the C++ uses `contains` and `at`, which model as `k in m` and `m[k]`. Neither changes the map.
// The contract says the key is missing, so the value is 0 and the result is the size.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

function wrap64(x: int): uint64 {
  (x % 0x1_0000_0000_0000_0000) as uint64
}

method count_after_read(m: map<int32, int32>, k: int32) returns (result: uint64)
  requires |m| < 0x1_0000_0000_0000_0000
  requires k !in m
  ensures result as int == |m|
{
  var v: int32 := if k in m then m[k] else 0;
  result := wrap64(|m| + (v as int));
}

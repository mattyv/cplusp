// Model A: the map is a Dafny map, and `m[k]` is a read.
// Dafny asks for a proof that k is in m. There is none, so the model is stricter than C++.
// The C++ does not read. It inserts a value-initialized element when k is missing.
// Dafny reports the postcondition too, because it holds for the value 0 only.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

function wrap64(x: int): uint64 {
  (x % 0x1_0000_0000_0000_0000) as uint64
}

method count_after_read(m: map<int32, int32>, k: int32) returns (result: uint64)
  requires |m| < 0x1_0000_0000_0000_0000
  ensures result as int == |m|
{
  var v := m[k];
  result := wrap64(|m| + (v as int));
}
